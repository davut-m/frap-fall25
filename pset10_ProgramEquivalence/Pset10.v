(*|
===========================================================
 6.512 Formal Reasoning About Programs, Fall 2025 - Pset 10
===========================================================
|*)

(* In this pset, you'll verify a *program-equivalence checker*.  The example we
 * consider is a pared-down version of CryptOpt (see
 * https://github.com/0xADE1A1DE/CryptOpt), a backend for the Fiat Cryptography
 * verified compiler (see https://github.com/mit-plv/fiat-crypto), which is
 * specialized to cryptographic arithmetic.  CryptOpt uses random program search
 * to modify assembly programs repeatedly, in search of faster variants.  That
 * search procedure is unverified, but, when it finishes, we run a checker to
 * confirm that the final, optimized assembly program computes the same
 * mathematical function as the original.  In fact, the same sort of checker can
 * be useful for e.g. using machine learning to generate many program variants
 * and filter out the ones that have not preserved behavior. *)

Require Import Pset10.Pset10Sig.
From Stdlib Require Import ZArith.
Local Open Scope Z_scope.

Module Impl.
  (** * Object language (assembly-style) *)

  (* Let's define the very simple programming language we'll work with. *)
  
  (** ** Syntax *)

  Inductive binop := Add | Mul | Sub.

  Inductive rhs :=
  | Const (n : Z)
  | Binop (b : binop) (x y : var).

  Record instr := Instr {
                      Lhs : var;
                      Rhs : rhs
                    }.

  Definition prog := list instr.

  (* In other words, a program is a sequence of simple instructions, each of
   * which assigns a value to a variable: either a constant or the result of
   * running a binary operation on the current values of two variables.  This
   * language retains some of the relevant characteristics of assembly language
   * while remaining pretty simple to work with. *)

  (** ** Semantics *)

  Definition valuation := fmap var Z.

  Definition evalBinop (b : binop) : Z -> Z -> Z :=
    match b with
    | Add => Z.add
    | Mul => Z.mul
    | Sub => Z.sub
    end.

  Notation "m $! k" := (match m $? k with Some n => n | None => 0 end) (at level 30).

  Definition evalRhs (r : rhs) (v : valuation) : Z :=
    match r with
    | Const n => n
    | Binop b x y => evalBinop b (v $! x) (v $! y)
    end.

  Definition evalInstr (v : valuation) (i : instr) : valuation :=
    v $+ (i.(Lhs), evalRhs i.(Rhs) v).

  Definition evalProg : prog -> valuation -> valuation :=
    fold_left evalInstr.
  (* Recall that [fold_left] is a general way to walk down a list in order,
   * applying a function to combine each data element into an accumulator.
   * (Here the accumulator is a valuation, extended with the effect of each
   * instruction.) *)

  (** * Symbolic execution *)

  (* OK, let's look at how we can check equivalence of two programs in this
   * language. *)

  (* First, similarly to our e-graph example from the AutomatedTheoremProving
   * lecture, we will maintain a kind of graph representation of program state
   * with careful sharing.  The nodes of that graph will be represented by
   * the integers [Z].  (Incidentally, Rocq represents [Z] relatively
   * efficiently in binary, while [nat] uses unary.) *)
  Definition node := Z.

  (* Every node is mapped to one of the following varieties of descriptions.
   * Note that this type is *not* recursive!  Nodes are described by reference
   * to other nodes, not full syntax trees of expressions. *)
  Inductive node_kind :=
  | SConst (n : Z)
    (* Known constant value *)
  | SVar (x : var)
    (* *Initial* value of a program variable (not value at current stage of
     * execution) *)
  | SAdd (n : Z) (args : list node)
    (* Addition operation, starting from constant [n] and adding in the values
     * of all the [args] *)
  | SMul (n : Z) (args : list node)
    (* Just like the above, but with multiplication instead of addition *)
  | SSub (x : node) (y : node)
    (* Subtracting the values of two nodes *).

  (* Why the asymmetrical treatment of addition/multiplication and subtraction?
   * The former are commutative and associative, allowing us to represent
   * compound expressions in natural *canonical* forms, when we sort arguments
   * by node IDs!  This sort of canonicalization will make it very cheap to
   * check whether two values are equal. *)

  (* OK, now we turn to the type of state that we maintain during symbolic
   * execution of programs. *)
  
  Definition nodes_in := fmap node_kind node.
  Definition nodes_out := fmap node node_kind.
  Definition varmap := fmap var node.

  Record sstate := SState {
                      NodesIn : nodes_in;
                      (* Maps each node kind seen so far its unique
                       * identifier *)
                      
                      NodesOut : nodes_out;
                      (* Dually, maps the identifiers back to their kinds *)
                      
                      NextNode : node;
                      (* The next node identifier we'll use, when the time comes
                       * to generate a new one *)

                      Vars : varmap
                      (* Associates program variables with nodes representing
                       * their *current*, not initial, values *)
                    }.

  (* A relatively tame operation to warm up with: coming up with a node
   * identifier for a given node kind, which may be a preexisting or a new
   * identifier *)
  Definition node_kind_in (st : sstate) (nk : node_kind) : sstate * node :=
    match st.(NodesIn) $? nk with
    | None => ({| NodesIn := st.(NodesIn) $+ (nk, st.(NextNode));
                 NodesOut := st.(NodesOut) $+ (st.(NextNode), nk);
                 NextNode := st.(NextNode) + 1;
                 Vars := st.(Vars) |},
                st.(NextNode))
    | Some nd => (st, nd)
    end.

  (* We will only use this dummy value in code that we prove is unreachable. *)
  Definition dummy := SConst 0.

  (* Here's an equality test analogous to the [==n] operator we've been using
   * with natural numbers. *)
  Infix "==z" := Z.eq_dec (no associativity, at level 50).

  (* Interpret a node as addition, as far as possible.  The addition will be
   * represented as a constant (could be zero) plus a sum of node values,
   * accounting for the two components of tuples that are returned. *)
  Definition symAddOf (st : sstate) (nd : node) : Z * list node :=
    match st.(NodesOut) $? nd with
    | Some (SAdd n args) =>
        (* Convenient: this node is already an addition, so we just copy out its
         * parameters. *)
        (n, args)
    | Some (SConst n) =>
        (* Second-best case: this node is a constant, which is easily
         * interpreted as a degenerate addition. *)
        (n, [])
    | _ =>
        (* Fallback: another degenerate addition, with just one node in the
         * summation *)
        (0, [nd])
    end.

  (* Multiplication is handled in a symmetrical way. *)
  Definition symMulOf (st : sstate) (nd : node) : Z * list node :=
    match st.(NodesOut) $? nd with
    | Some (SMul n args) => (n, args)
    | Some (SConst n) => (n, [])
    | _ => (1, [nd])
    end.

  Definition isNil {A} (ls : list A) :=
    match ls with
    | nil => true
    | _ => false
    end.

  (* Here's the most interesting function.  It interprets the righthand side of
   * an instruction as a node kind, referencing the state. *)
  Definition kindOfRhs (st : sstate) (r : rhs) : node_kind :=
    match r with
    | Const n => SConst n
    | Binop Sub x y =>
        match st.(Vars) $? x, st.(Vars) $? y with
        | Some nx, Some ny =>
            (* Both variables are present in the state and assigned to these
             * node IDs.  (We will prove that the other case is unreachable. *)
            match st.(NodesOut) $? nx, st.(NodesOut) $? ny with
            | Some nkx, Some (SConst n) =>
                (* Ah, the second argument is a constant. *)
                if n ==z 0 then
                  (* Even better, the constant is zero, so the kind of the first
                   * operand is reusable to represent the subtraction. *)
                  nkx
                else
                  (* When no special case applies, we just build a subtraction
                   * kind. *)
                  SSub nx ny
            | _, _ => SSub nx ny
            end
        | _, _ => dummy
        end
    | Binop Add x y =>
        match st.(Vars) $? x, st.(Vars) $? y with
        | Some nx, Some ny =>
            (* Interpret both operand nodes as additions. *)
            let (n1, args1) := symAddOf st nx in
            let (n2, args2) := symAddOf st ny in
            (* Use code from a standard-library implementation of merge sort, to
             * combine the two argument lists while preserving *sorted* order
             * that we use to make representations canonical up to associativity
             * and commutativity. *)
            let args := ZSort.merge args1 args2 in
            if isNil args then
              (* Oh, if there are no general nodes in the overall sum, then we
               * just added two constants, which produces another constant. *)
              SConst (n1 + n2)
            else
              (* Otherwise, we have this boring generic case. *)
              SAdd (n1 + n2) args
        | _, _ => dummy
        end
    | Binop Mul x y =>
        (* Multiplication is highly symmetrical with addition. *)
        match st.(Vars) $? x, st.(Vars) $? y with
        | Some nx, Some ny =>
            let (n1, args1) := symMulOf st nx in
            let (n2, args2) := symMulOf st ny in
            let args := ZSort.merge args1 args2 in
            if isNil args then
              SConst (n1 * n2)
            else
              SMul (n1 * n2) args
        | _, _ => dummy
        end
    end.

  (* To interpret an instruction, find the node kind for its righthand side,
   * then be sure it's represented in the state, using its node ID to assign to
   * the lefthand side. *)
  Definition symInstr (st : sstate) (i : instr) : sstate :=
    let (st, n) := node_kind_in st (kindOfRhs st i.(Rhs)) in
    {| NodesIn := st.(NodesIn);
      NodesOut := st.(NodesOut);
      NextNode := st.(NextNode);
      Vars := st.(Vars) $+ (i.(Lhs), n) |}.

  (* Symbolically executing a program just iterates execution of
   * instructions. *)
  Definition symProg : prog -> sstate -> sstate :=
    fold_left symInstr.

  (* For simplicity, let's say that these three variables store the inputs to a
   * program. *)
  Definition inputs := {"a", "b", "c"}.

  (* So the following initial state for symbolic execution is proper. *)
  Definition initial : sstate :=
    {| NodesIn := $0 $+ (SVar "a", 0) $+ (SVar "b", 1) $+ (SVar "c", 2);
      NodesOut := $0 $+ (0, SVar "a") $+ (1, SVar "b") $+ (2, SVar "c");
      NextNode := 3;
      Vars := $0 $+ ("a", 0) $+ ("b", 1) $+ ("c", 2) |}.

  (* In checking program equivalence, we will symbolically execute both
   * programs, using this function to reset just the variables component of
   * state between programs.  The idea is that we quite intentionally share a
   * canonicalized representation of terms, allowing us to check provable
   * equality of subterms between the two programs just by checking that they
   * get internalized into identical nodes. *)
  Definition redoVars (st : sstate) : sstate :=
    {| NodesIn := st.(NodesIn);
      NodesOut := st.(NodesOut);
      NextNode := st.(NextNode);
      Vars := $0 $+ ("a", 0) $+ ("b", 1) $+ ("c", 2) |}.

  (* The overall checker: *)
  Definition equivalent (pr1 pr2 : prog) : bool :=
    let st := initial in
    let st := symProg pr1 st in
    let out1 := st.(Vars) $? "out" in
    let st := redoVars st in
    let st := symProg pr2 st in
    let out2 := st.(Vars) $? "out" in
    match out1, out2 with
    | Some out1, Some out2 =>
        (* If this Boolean equality test succeeds, then the outputs were
         * internalized to the same graph node, and we have proved program
         * equivalence! *)
        Z.eqb out1 out2
    | _, _ => false
    end.

  (* Here are a few small examples.  We have commented out the code to run the
   * checker, because it runs very slowly.  The reason is that we use FRAP
   * finite maps, which are actually axiomatized instead of defined
   * computationally, which prevents us from using the built-in interpreter to
   * do all of the execution work efficiently. *)
   
  Example ex1a := [Instr "x" (Const 1);
                   Instr "y" (Const 2);
                   Instr "out" (Binop Add "x" "y")].
  Example ex1b := [Instr "out" (Const 3)].

  (*Goal equivalent ex1a ex1b = true.
  Proof.
    repeat (compute; simplify).
    reflexivity.
  Qed.*)

  Example ex2a := [Instr "x" (Const 1);
                   Instr "y" (Const 2);
                   Instr "out" (Binop Add "x" "y")].
  Example ex2b := [Instr "out" (Const 4)].

  (*Goal equivalent ex2a ex2b = false.
  Proof.
    repeat (compute; simplify).
    reflexivity.
  Qed.*)

  Example ex3a := [Instr "out" (Binop Add "x" "y")].
  Example ex3b := [Instr "out" (Binop Add "y" "x")].

  (*Goal equivalent ex3a ex3b = true.
  Proof.
    repeat (compute; simplify).
    reflexivity.
  Qed.*)

  Example ex4a := [Instr "out" (Binop Add "a" "b");
                   Instr "k" (Const 0);
                   Instr "out" (Binop Add "out" "k");
                   Instr "out" (Binop Add "c" "out")].
  Example ex4b := [Instr "u" (Binop Add "b" "c");
                   Instr "out" (Binop Add "u" "a")].

  (*Goal equivalent ex4a ex4b [] "a" = true.
  Proof.
    repeat (compute; simplify).
    reflexivity.
  Qed.*)


  (** * Correctness *)

  (* To make sure symbolic execution tracks enough variables, we need to define
   * which variables an instruction reads. *)
  
  Definition rhsReads (r : rhs) : set var :=
    match r with
    | Const _ => {}
    | Binop _ x y => {x, y}
    end.

  Fixpoint progReads (pr : prog) : set var :=
    match pr with
    | [] => {}
    | Instr lhs rhs :: pr' => rhsReads rhs \cup (progReads pr' \setminus {lhs})
    end.
  (* Note the subtlety above: instructions are not considered to read variables
   * that were set by earlier instructions.  We only want to capture which
   * variable reads depend on the initial values of variables. *)



  Theorem equivalent_correct : forall pr1 pr2,
      equivalent pr1 pr2 = true
      -> (progReads pr1 \cup progReads pr2) \subseteq inputs
      -> forall v, evalProg pr1 v $! "out" = evalProg pr2 v $! "out".
  Proof.
  Admitted.
End Impl.

Module ImplCorrect : Pset10Sig.S := Impl.

(*|
Authors:

- Adam Chlipala
|*)
