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


(* | We're glad to give full credit for any proof of the designated main theorem,
  but it's a relatively involved proof, so we also give the great majority of a
  solution below, with notes on how we will assign partial credit for the
  unproved lemmas that we have left. *)

  (* The following type will play a crucial role: it assigns semantic meanings
   * to all graph nodes. *)
  Definition nodeVals := fmap node Z.

  (* Interpreting our node kinds w.r.t. node values and variable values is
   * fairly straightforward. *)

  Definition sum := fold_left Z.add.
  Definition product := fold_left Z.mul.

  Definition evalNodeKind (nvs : nodeVals) (v : valuation) (nk : node_kind) : Z :=
    match nk with
    | SConst n => n
    | SVar x => v $! x
    | SAdd n nds => sum (map (fun nd => nvs $! nd) nds) n
    | SMul n nds => product (map (fun nd => nvs $! nd) nds) n
    | SSub nd1 nd2 => nvs $! nd1 - nvs $! nd2
    end.

  (* It's useful to have a way to state bounds on which node identifiers may
   * appear in a node kind. *)
  Definition nodeKindInBounds (bound : Z) (nk : node_kind) :=
    match nk with
    | SConst _ | SVar _ => True
    | SAdd _ args | SMul _ args => List.Forall (fun arg => arg < bound) args
    | SSub x y => x < bound /\ y < bound
    end.

  (* Here is the main invariant we maintain as we execute, connecting: *)
  Record compat
         (st : sstate)      (* symbolic state *)
         (v0 v : valuation) (* initial and current variable values *)
         (nvs : nodeVals)   (* node values *) := {
      OutToIn : forall nd nk, st.(NodesOut) $? nd = Some nk
                              -> st.(NodesIn) $? nk = Some nd;
      InToOut : forall nd nk, st.(NodesIn) $? nk = Some nd
                              -> st.(NodesOut) $? nd = Some nk;
      InBounds1 : forall nd nk, st.(NodesOut) $? nd = Some nk
                                -> nd < st.(NextNode);
      InBounds2 : forall nd nk, st.(NodesIn) $? nk = Some nd
                                -> nodeKindInBounds st.(NextNode) nk;
      OutVals : forall nd nk, st.(NodesOut) $? nd = Some nk
                              -> nvs $? nd = Some (evalNodeKind nvs v0 nk);
      OutValsInv : forall nd, nvs $? nd <> None
                              -> st.(NodesOut) $? nd <> None;
      VarToNode : forall x nd, st.(Vars) $? x = Some nd
                             -> st.(NodesOut) $? nd <> None;
      VarToNodevals : forall x nd, st.(Vars) $? x = Some nd
                             -> nvs $? nd = Some (v $! x)
    }.
  (* Note that we have defined a predicate as a record, which basically means
   * the predicate is a big "and" of the different named properties.  This
   * syntax actually desugars into an inductive predicate definition with a
   * single constructor, plus a projection function per record field.  Try
   * [Check]ing the field names to see how that works. *)

  Local Hint Resolve VarToNode : core.

  Lemma varIsFine : forall (s : set var) (m : fmap var node) x,
      s \subseteq dom m
      -> m $? x = None
      -> x \in s
      -> False.
  Proof.
    simplify.
    apply lookup_None_dom in H0.
    sets.
  Qed.

  Local Hint Extern 1 False => (eapply varIsFine; [ eassumption | eassumption | sets ]) : core.

  Lemma nvs_anything : forall (nvs : nodeVals) nd n,
      nvs $? nd = Some n
      -> nvs $? nd = Some (nvs $! nd).
  Proof.
    simplify.
    rewrite H.
    reflexivity.
  Qed.

  Local Hint Resolve nvs_anything : core.

  (* OK, our first correctness theorem for a helper function: *)
  (*[15%]*)Lemma symAddOf_correct : forall st v0 v nvs n z l,
      compat st v0 v nvs
      -> st.(NodesOut) $? n <> None
      -> symAddOf st n = (z, l)
      -> nvs $? n = Some (sum (map (fun nd => nvs $! nd) l) z).
  Proof.
    unfold symAddOf; simplify.
    cases (st.(NodesOut) $? n); simplify.
    - cases n0; simplify;
      invert H1;
      pose proof (OutVals st v0 v nvs H n _ Heq);
      eauto.
    - equality.
  Qed.

  (* Symmetrical one for multiplication: *)
  (*[15%]*)Lemma symMulOf_correct : forall st v0 v nvs n z l,
      compat st v0 v nvs
      -> st.(NodesOut) $? n <> None
      -> symMulOf st n = (z, l)
      -> nvs $? n = Some (product (map (fun nd => nvs $! nd) l) z).
  Proof.
    unfold symMulOf; simplify.
    cases (st.(NodesOut) $? n); simplify.
    - cases n0; simplify;
      invert H1;
      pose proof (OutVals st v0 v nvs H n _ Heq);
      eauto; simplify;
      cases (nvs $! n); invert Heq0; eauto.
    - equality.
  Qed.

  (* We will need to know that merging sums and products has the expected
   * effects, and one way to go about it is proving properties generically for
   * associative-commutative operators. *)
  Section associative_commutative.
    Variable f : Z -> Z -> Z.
    Hypothesis commutative : forall x y, f x y = f y x.
    Hypothesis associative : forall x y z, f (f x y) z = f x (f y z).

    Variable g : Z -> Z.

    Lemma fold_left_permutation : forall l l' a,
        Permutation.Permutation l l' -> fold_left f l a = fold_left f l' a.
    Proof.
      simplify; revert a.
      induction H; eauto; simplify.
      - rewrite associative.
        rewrite commutative.
        rewrite associative.
        rewrite (commutative a x).
        rewrite commutative.
        eauto.
      - rewrite IHPermutation1, IHPermutation2; auto.
    Qed.

    Lemma fold_left_f_merge1 : forall l a b,
        fold_left f l (f a b) = f (fold_left f l a) b.
    Proof.
      induction l; simpl; auto.
      intros.
      rewrite associative.
      rewrite <-IHl.
      rewrite associative.
      rewrite (commutative b a).
      eauto.
    Qed.

    Lemma fold_left_f_merge3 : forall l a b,
        fold_left f l (f a b) = f a (fold_left f l b).
    Proof.
      intros.
      rewrite commutative.
      rewrite fold_left_f_merge1.
      rewrite commutative.
      eauto.
    Qed.

    Lemma merge_dumb: forall l,
        ZSort.merge [] l = l.
    Proof.
      induct l.
      - simplify; eauto.
      - simplify; eauto.
    Qed.

    Lemma perm_swap_app : forall (A : Type) (x y : A) (l1 l2 : list A),
        Permutation.Permutation (y :: x :: l1 ++ l2) (x :: l1 ++ y :: l2).
    Proof.
      simplify.
      apply Permutation.perm_trans with (l' := x :: y :: l1 ++ l2).
      - apply Permutation.perm_swap.
      - rewrite app_comm_cons.
        rewrite Permutation.perm_skip; eauto.
        eapply Permutation.Permutation_cons_app; eauto.
    Qed.


    Lemma merge_permutation : forall l1 l2,
        Permutation.Permutation (ZSort.merge l1 l2) (l1 ++ l2).
    Proof.
      induct l1; intros.
      - replace ([] ++ l2) with l2 by (simplify; eauto).
        rewrite merge_dumb.
        eauto.
      - induct l2.
        + simplify. rewrite app_nil_r. apply Permutation.Permutation_refl.
        + simpl.
          destruct (Z.leb a a0).
          ++ simplify. eapply Permutation.perm_skip. apply IHl1.
          ++ eapply Permutation.perm_skip in IHl2.
             simpl in IHl2.
             eapply Permutation.perm_trans.
             eapply IHl2.
             eapply perm_swap_app.
    Qed.

    (*[35%]*)Lemma merge_combine : forall l1 n1 l2 n2,
        fold_left f (map g (ZSort.merge l1 l2)) (f n1 n2)
        = f (fold_left f (map g l1) n1) (fold_left f (map g l2) n2).
    Proof.
      intros.
      rewrite fold_left_permutation with (l' := map g (l1 ++ l2)).
      - rewrite map_app.
        rewrite fold_left_app.
        rewrite fold_left_f_merge1.
        rewrite fold_left_f_merge3.
        eauto.
      - rewrite merge_permutation.
        eauto.
    Qed.

    (* We proved this one via several more-general lemmas. *)
  End associative_commutative.

  Lemma VarVals3 : forall st v0 v nvs x n n1,
      compat st v0 v nvs
      -> Vars st $? x = Some n
      -> NodesOut st $? n = Some n1
      -> evalNodeKind nvs v0 n1 = v $! x.
  Proof.
    simplify.
    eapply VarToNodevals in H0; eauto.
    eapply OutVals in H1; eauto.
    equality.
  Qed.

  Local Hint Resolve VarVals3 : core.


  (* Another helper's correctness theorem *)
  (*[35%]*)Lemma kindOfRhs_correct : forall st r nvs v0 v,
      compat st v0 v nvs
      -> rhsReads r \subseteq dom st.(Vars)
      -> evalNodeKind nvs v0 (kindOfRhs st r) = evalRhs r v.
  Proof.
    simplify.
    unfold kindOfRhs, evalRhs.

    cases r; simplify.
    - equality. (* "* = ++". "-- = ++" *)
    - cases b; simplify.
      + cases (Vars st $? x); simplify.
        ++ cases (Vars st $? y); simplify.
          -- cases (symAddOf st n).
            cases (symAddOf st n0).
            cases (isNil (ZSort.merge l l0)); simplify.
            ---
                pose proof (VarToNode st v0 v nvs H x n Heq).
                pose proof (VarToNode st v0 v nvs H y n0 Heq0).
                pose proof (symAddOf_correct st v0 v nvs n _ _ H H1 Heq1).
                pose proof (symAddOf_correct st v0 v nvs n0 _ _ H H2 Heq2).
                pose proof (VarToNodevals st v0 v nvs H x n Heq).
                pose proof (VarToNodevals st v0 v nvs H y n0 Heq0).

                rewrite H5 in H3.
                rewrite H6 in H4.
                invert H3.
                invert H4.
                rewrite H7, H8.

                unfold sum.

                unfold isNil in Heq3.
                cases (ZSort.merge l l0).
                assert (sum (map (fun nd : node => nvs $! nd) (ZSort.merge l l0)) (z+z0) = z+z0).
                rewrite Heq4.
                simplify.
                equality.
                invert H3.

                eapply merge_combine.
                simplify.
                linear_arithmetic.

                simplify.
                linear_arithmetic.

                exfalso. linear_arithmetic.
            ---
                pose proof (VarToNode st v0 v nvs H x n Heq).
                pose proof (VarToNode st v0 v nvs H y n0 Heq0).
                pose proof (symAddOf_correct st v0 v nvs n _ _ H H1 Heq1).
                pose proof (symAddOf_correct st v0 v nvs n0 _ _ H H2 Heq2).
                pose proof (VarToNodevals st v0 v nvs H x n Heq).
                pose proof (VarToNodevals st v0 v nvs H y n0 Heq0).

                rewrite H5 in H3.
                rewrite H6 in H4.
                invert H3.
                invert H4.
                rewrite H7, H8.
                unfold sum.
                eapply merge_combine; eauto; simplify; linear_arithmetic.
          -- exfalso; eauto.
        ++ exfalso; eauto.
      + cases (Vars st $? x); simplify.
        ++ cases (Vars st $? y); simplify.
          -- cases (symMulOf st n).
            cases (symMulOf st n0).
            cases (isNil (ZSort.merge l l0)); simplify.
            ---
                pose proof (VarToNode st v0 v nvs H x n Heq).
                pose proof (VarToNode st v0 v nvs H y n0 Heq0).
                pose proof (symMulOf_correct st v0 v nvs n _ _ H H1 Heq1).
                pose proof (symMulOf_correct st v0 v nvs n0 _ _ H H2 Heq2).
                pose proof (VarToNodevals st v0 v nvs H x n Heq).
                pose proof (VarToNodevals st v0 v nvs H y n0 Heq0).

                rewrite H5 in H3.
                rewrite H6 in H4.
                invert H3.
                invert H4.
                rewrite H7, H8.

                unfold product.
                unfold isNil in Heq3.
                cases (ZSort.merge l l0).

                assert (product (map (fun nd : node => nvs $! nd) (ZSort.merge l l0)) (z*z0) = z*z0).
                rewrite Heq4.
                simplify.
                equality.
                invert H3.

                eapply merge_combine.
                simplify.
                linear_arithmetic.

                simplify.
                linear_arithmetic.

                exfalso. linear_arithmetic.
            ---
                pose proof (VarToNode st v0 v nvs H x n Heq).
                pose proof (VarToNode st v0 v nvs H y n0 Heq0).
                pose proof (symMulOf_correct st v0 v nvs n _ _ H H1 Heq1).
                pose proof (symMulOf_correct st v0 v nvs n0 _ _ H H2 Heq2).
                pose proof (VarToNodevals st v0 v nvs H x n Heq).
                pose proof (VarToNodevals st v0 v nvs H y n0 Heq0).

                rewrite H5 in H3.
                rewrite H6 in H4.
                invert H3.
                invert H4.
                rewrite H7, H8.

                unfold product.

                eapply merge_combine; eauto; simplify; linear_arithmetic.
          -- exfalso; eauto.
        ++ exfalso; eauto.

      + cases (Vars st $? x); simplify.
        ++ cases (Vars st $? y); simplify.
          -- cases (NodesOut st $? n).
            --- cases (NodesOut st $? n0).
              +++ cases (n2).
                  cases (n2 ==z 0).
                  pose proof (VarToNode st v0 v nvs H x n Heq).
                  pose proof (VarToNode st v0 v nvs H y n0 Heq0).
                  pose proof (VarToNodevals st v0 v nvs H x n Heq).
                  pose proof (VarToNodevals st v0 v nvs H y n0 Heq0).
                  pose proof (OutVals st v0 v nvs H n n1 Heq1).
                  pose proof (OutVals st v0 v nvs H n0 (SConst n2) Heq2).
                  invert H5.
                  invert H6.
                  rewrite H3 in H8.
                  invert H8.
                  rewrite H7 in H4.
                  invert H4.
                  linear_arithmetic.

                  pose proof (VarToNode st v0 v nvs H x n Heq).
                  pose proof (VarToNode st v0 v nvs H y n0 Heq0).
                  pose proof (VarToNodevals st v0 v nvs H x n Heq).
                  pose proof (VarToNodevals st v0 v nvs H y n0 Heq0).
                  pose proof (OutVals st v0 v nvs H n n1 Heq1).
                  pose proof (OutVals st v0 v nvs H n0 (SConst n2) Heq2).
                  invert H5.
                  invert H6.
                  rewrite H3 in H8.
                  invert H8.
                  rewrite H7 in H4.
                  invert H4.
                  simplify.
                  rewrite H3.
                  rewrite H7.
                  linear_arithmetic.

                  pose proof (VarToNode st v0 v nvs H x n Heq).
                  pose proof (VarToNode st v0 v nvs H y n0 Heq0).
                  pose proof (VarToNodevals st v0 v nvs H x n Heq).
                  pose proof (VarToNodevals st v0 v nvs H y n0 Heq0).
                  pose proof (OutVals st v0 v nvs H n n1 Heq1).
                  pose proof (OutVals st v0 v nvs H n0 (SVar x0) Heq2).
                  invert H5.
                  invert H6.
                  rewrite H3 in H8.
                  invert H8.
                  rewrite H7 in H4.
                  invert H4.
                  simplify.
                  rewrite H3.
                  rewrite H7.
                  linear_arithmetic.

                  pose proof (VarToNode st v0 v nvs H x n Heq).
                  pose proof (VarToNode st v0 v nvs H y n0 Heq0).
                  pose proof (VarToNodevals st v0 v nvs H x n Heq).
                  pose proof (VarToNodevals st v0 v nvs H y n0 Heq0).
                  pose proof (OutVals st v0 v nvs H n n1 Heq1).
                  pose proof (OutVals st v0 v nvs H n0 (SAdd n2 args) Heq2).
                  invert H5.
                  invert H6.
                  rewrite H3 in H8.
                  invert H8.
                  rewrite H7 in H4.
                  invert H4.
                  simplify.
                  rewrite H3.
                  rewrite H7.
                  linear_arithmetic.

                  pose proof (VarToNode st v0 v nvs H x n Heq).
                  pose proof (VarToNode st v0 v nvs H y n0 Heq0).
                  pose proof (VarToNodevals st v0 v nvs H x n Heq).
                  pose proof (VarToNodevals st v0 v nvs H y n0 Heq0).
                  pose proof (OutVals st v0 v nvs H n n1 Heq1).
                  pose proof (OutVals st v0 v nvs H n0 (SMul n2 args) Heq2).
                  invert H5.
                  invert H6.
                  rewrite H3 in H8.
                  invert H8.
                  rewrite H7 in H4.
                  invert H4.
                  simplify.
                  rewrite H3.
                  rewrite H7.
                  linear_arithmetic.


                  pose proof (VarToNode st v0 v nvs H x n Heq).
                  pose proof (VarToNode st v0 v nvs H y n0 Heq0).
                  pose proof (VarToNodevals st v0 v nvs H x n Heq).
                  pose proof (VarToNodevals st v0 v nvs H y n0 Heq0).
                  pose proof (OutVals st v0 v nvs H n n1 Heq1).
                  pose proof (OutVals st v0 v nvs H n0 (SSub x0 y0) Heq2).
                  invert H5.
                  invert H6.
                  rewrite H3 in H8.
                  invert H8.
                  rewrite H7 in H4.
                  invert H4.
                  simplify.
                  rewrite H3.
                  rewrite H7.
                  linear_arithmetic.
              +++
                  pose proof (VarToNode st v0 v nvs H x n Heq).
                  pose proof (VarToNode st v0 v nvs H y n0 Heq0).
                  pose proof (VarToNodevals st v0 v nvs H x n Heq).
                  pose proof (VarToNodevals st v0 v nvs H y n0 Heq0).

                  exfalso. eauto.
            ---
                pose proof (VarToNode st v0 v nvs H x n Heq).
                pose proof (VarToNode st v0 v nvs H y n0 Heq0).
                pose proof (VarToNodevals st v0 v nvs H x n Heq).
                pose proof (VarToNodevals st v0 v nvs H y n0 Heq0).

                exfalso. eauto.
          --  pose proof (VarToNode st v0 v nvs H x n Heq).
              pose proof (VarToNodevals st v0 v nvs H x n Heq).

              eapply varIsFine in H0; eauto.
              exfalso. eauto.

              exfalso. eauto.
        ++  eapply varIsFine in H0; eauto.
            exfalso. eauto.

            exfalso. eauto.
  Qed.

  (* From this point out, things are getting more complicated, and we're not
   * going to narrate the details (and all the proofs are already included). *)

  Local Hint Resolve InToOut OutVals : core.

  Definition node_kind_eq_dec : forall nk1 nk2 : node_kind, sumbool (nk1 = nk2) (nk1 <> nk2).
  Proof.
    decide equality.
    apply Z.eq_dec.
    apply var_eq.
    apply list_eq_dec; apply Z.eq_dec.
    apply Z.eq_dec.
    apply list_eq_dec; apply Z.eq_dec.
    apply Z.eq_dec.
    apply Z.eq_dec.
    apply Z.eq_dec.
  Qed.

  Lemma nodeKindInBounds_mono : forall n n' nk,
      nodeKindInBounds n nk
      -> n <= n'
      -> nodeKindInBounds n' nk.
  Proof.
    simplify; cases nk; simplify; propositional; try linear_arithmetic.
    eapply Forall_impl; eauto; simplify; linear_arithmetic.
    eapply Forall_impl; eauto; simplify; linear_arithmetic.
  Qed.

  Lemma map_bound : forall bound (nvs1 nvs2 : nodeVals) args,
      Forall (fun arg => arg < bound) args
      -> (forall k, k < bound -> nvs1 $? k = nvs2 $? k)
      -> map (fun nd => nvs1 $! nd) args = map (fun nd => nvs2 $! nd) args.
  Proof.
    induct args; simplify; auto.

    invert H.
    f_equal; auto.
    rewrite H0 by assumption.
    reflexivity.
  Qed.

  Lemma evalNodeKind_relevant : forall bound nk nvs1 nvs2 v,
      nodeKindInBounds bound nk
      -> (forall k, k < bound -> nvs1 $? k = nvs2 $? k)
      -> evalNodeKind nvs1 v nk = evalNodeKind nvs2 v nk.
  Proof.
    simplify.
    cases nk; simplify; propositional; auto.

    f_equal.
    eapply map_bound; eauto.

    f_equal.
    eapply map_bound; eauto.

    rewrite !H0 by assumption.
    reflexivity.
  Qed.

  Local Hint Resolve InBounds2 OutToIn includes_refl : core.

  Lemma includes_add : forall A B (m : fmap A B) k v,
      m $? k = None
      -> m $<= m $+ (k, v).
  Proof.
    simplify.
    apply includes_intro.
    simplify.
    assumption.
  Qed.

  Local Hint Resolve includes_add : core.

  Definition node_kind_in_correct : forall st v0 v nvs nk,
      compat st v0 v nvs
      -> nodeKindInBounds st.(NextNode) nk
      -> exists nvs', nvs $<= nvs'
                      /\ compat (fst (node_kind_in st nk)) v0 v nvs'
                      /\ (fst (node_kind_in st nk)).(NodesOut) $? snd (node_kind_in st nk) <> None
                      /\ nvs' $? snd (node_kind_in st nk) = Some (evalNodeKind nvs' v0 nk).
  Proof.
    unfold node_kind_in; simplify.
    cases (NodesIn st $? nk); simplify.

    exists nvs; propositional; eauto.
    eapply InToOut in Heq; eauto.
    equality.

    exists (nvs $+ (st.(NextNode), evalNodeKind nvs v0 nk)).
    simplify; propositional; try equality.

    apply includes_add.
    cases (nvs $? NextNode st); auto.
    assert (nvs $? NextNode st <> None) by equality.
    eapply OutValsInv in H1; eauto.
    cases (NodesOut st $? NextNode st); try equality.
    eapply InBounds1 in Heq1; eauto.
    linear_arithmetic.

    constructor; simplify; eauto using InBounds1.

    cases (node_kind_eq_dec nk nk0); subst; simplify.
    cases (Z.eq_dec (NextNode st) nd); subst; simplify; auto.
    eapply OutToIn in H1; eauto; equality.
    cases (Z.eq_dec (NextNode st) nd); subst; simplify; auto.
    equality.
    eauto using OutToIn.

    cases (Z.eq_dec (NextNode st) nd); subst; simplify.
    cases (node_kind_eq_dec nk nk0); subst; simplify; auto.
    eapply InToOut in H1; eauto.
    eapply InBounds1 in H1; eauto.
    linear_arithmetic.
    cases (node_kind_eq_dec nk nk0); subst; simplify; auto.
    equality.
    eauto.

    cases (Z.eq_dec (NextNode st) nd); subst; simplify.
    linear_arithmetic.
    eapply InBounds1 in H1; eauto.
    linear_arithmetic.

    cases (node_kind_eq_dec nk nk0); subst; simplify.
    eapply nodeKindInBounds_mono; eauto.
    linear_arithmetic.
    eapply InBounds2 in H1; eauto.
    eapply nodeKindInBounds_mono; eauto.
    linear_arithmetic.

    cases (Z.eq_dec (NextNode st) nd); subst; simplify.
    invert H1.
    f_equal.
    eapply evalNodeKind_relevant; eauto.
    simplify.
    assert (k <> NextNode st) by linear_arithmetic.
    simplify.
    reflexivity.
    erewrite OutVals; eauto.
    f_equal.
    eapply evalNodeKind_relevant; eauto.
    simplify.
    cases (Z.eq_dec (NextNode st) k); subst; simplify; auto.
    linear_arithmetic.

    cases (Z.eq_dec (NextNode st) nd); subst; simplify; eauto; try equality.
    eapply OutValsInv in H1; eauto.

    cases (Z.eq_dec (NextNode st) nd); subst; simplify; eauto.
    eapply VarToNode in H1; eauto.
    cases (NodesOut st $? NextNode st); equality.

    assert (nd <> NextNode st).
    eapply VarToNode in H1; eauto.
    cases (NodesOut st $? NextNode st); simplify; try equality.
    eapply InBounds1 in Heq0; eauto.
    linear_arithmetic.
    simplify.
    eauto using VarToNodevals.

    f_equal.
    eapply evalNodeKind_relevant; eauto.
    simplify.
    assert (k <> NextNode st) by linear_arithmetic.
    simplify.
    reflexivity.
  Qed.

  Lemma VarInBounds : forall st v0 v nvs x n,
      compat st v0 v nvs
      -> Vars st $? x = Some n
      -> n < NextNode st.
  Proof.
    simplify.
    eapply VarToNode in H0; eauto.
    cases (NodesOut st $? n); try equality.
    eapply InBounds1; eauto.
  Qed.

  Local Hint Resolve VarInBounds : core.

  Lemma symAddOf_bounds : forall st v0 v nvs n z l,
      compat st v0 v nvs
      -> symAddOf st n = (z, l)
      -> st.(NodesOut) $? n <> None
      -> Forall (fun arg => arg < st.(NextNode)) l.
  Proof.
    unfold symAddOf; simplify.
    repeat match goal with
           | [ H : (_, _) = (_, _) |- _ ] => invert H
           | [ H : match ?E with _ => _ end = _ |- _ ] => cases E
           | [ H : _.(NodesOut) $? _ = Some _ |- _ ] => solve [ eapply InBounds1 in H; eauto ]
           end; auto; try equality.
    eapply OutToIn in Heq; eauto.
    eapply InBounds2 in Heq; eauto.
  Qed.

  Lemma symMulOf_bounds : forall st v0 v nvs n z l,
      compat st v0 v nvs
      -> symMulOf st n = (z, l)
      -> st.(NodesOut) $? n <> None
      -> Forall (fun arg => arg < st.(NextNode)) l.
  Proof.
    unfold symMulOf; simplify.
    repeat match goal with
           | [ H : (_, _) = (_, _) |- _ ] => invert H
           | [ H : match ?E with _ => _ end = _ |- _ ] => cases E
           | [ H : _.(NodesOut) $? _ = Some _ |- _ ] => solve [ eapply InBounds1 in H; eauto ]
           end; auto; try equality.
    eapply OutToIn in Heq; eauto.
    eapply InBounds2 in Heq; eauto.
  Qed.

  Lemma merge_property : forall P l1 l2,
      Forall P l1
      -> Forall P l2
      -> Forall P (ZSort.merge l1 l2).
  Proof.
    induct l1; induct l2; simplify; auto.
    invert H.
    invert H0.
    cases (a <=? a0); auto.
  Qed.

  Local Hint Resolve merge_property symAddOf_bounds symMulOf_bounds : core.

  Lemma in_bounds_rhs : forall st v0 v nvs r,
      compat st v0 v nvs
      -> rhsReads r \subseteq dom st.(Vars)
      -> nodeKindInBounds st.(NextNode) (kindOfRhs st r).
  Proof.
    simplify; cases r; simplify; auto.
    repeat match goal with
           | [ |- nodeKindInBounds _ (match ?E with _ => _ end) ] => cases E
           end; simplify; propositional; eauto 6.
  Qed.

  Local Hint Resolve in_bounds_rhs : core.

  Lemma node_kind_in_Vars : forall st nk st' nd,
      node_kind_in st nk = (st', nd)
      -> Vars st' = Vars st.
  Proof.
    unfold node_kind_in; simplify.
    cases (NodesIn st $? nk); try equality.
    invert H.
    reflexivity.
  Qed.

  Lemma node_kind_in_NodesOut : forall st nk st' nd v0 v nvs,
      compat st v0 v nvs
      -> node_kind_in st nk = (st', nd)
      -> st.(NodesOut) $<= st'.(NodesOut).
  Proof.
    unfold node_kind_in; simplify.
    cases (NodesIn st $? nk); try equality.
    invert H0.
    auto.
    invert H0.
    simplify.
    apply includes_add.
    cases (NodesOut st $? NextNode st); auto.
    eapply InBounds1 in Heq0; eauto.
    linear_arithmetic.
  Qed.

  Local Hint Resolve node_kind_in_Vars node_kind_in_NodesOut : core.

  Lemma symAddOf_mono : forall st v0 v nvs nd st' x,
      compat st v0 v nvs
      -> st.(NodesOut) $<= st'.(NodesOut)
      -> st.(Vars) = st'.(Vars)
      -> st.(Vars) $? x = Some nd
      -> symAddOf st' nd = symAddOf st nd.
  Proof.
    unfold symAddOf; simplify.
    cases (NodesOut st $? nd).
    erewrite includes_lookup; eauto.
    eapply VarToNode in H2; eauto.
    equality.
  Qed.

  Lemma symMulOf_mono : forall st v0 v nvs nd st' x,
      compat st v0 v nvs
      -> st.(NodesOut) $<= st'.(NodesOut)
      -> st.(Vars) = st'.(Vars)
      -> st.(Vars) $? x = Some nd
      -> symMulOf st' nd = symMulOf st nd.
  Proof.
    unfold symMulOf; simplify.
    cases (NodesOut st $? nd).
    erewrite includes_lookup; eauto.
    eapply VarToNode in H2; eauto.
    equality.
  Qed.

  Lemma kindOfRhs_mono : forall st v0 v nvs r st',
      compat st v0 v nvs
      -> rhsReads r \subseteq dom (Vars st)
      -> st.(NodesOut) $<= st'.(NodesOut)
      -> st.(Vars) = st'.(Vars)
      -> kindOfRhs st' r = kindOfRhs st r.
  Proof.
    simplify; case r; simplify; auto.
    rewrite <- H2.
    repeat match goal with
           | [ |- _ = match ?E with _ => _ end ] => cases E
           end; auto.

    erewrite symAddOf_mono by eauto.
    rewrite Heq1.
    erewrite symAddOf_mono by eauto.
    rewrite Heq2.
    rewrite Heq3.
    reflexivity.

    erewrite symAddOf_mono by eauto.
    rewrite Heq1.
    erewrite symAddOf_mono by eauto.
    rewrite Heq2.
    rewrite Heq3.
    reflexivity.

    erewrite symMulOf_mono by eauto.
    rewrite Heq1.
    erewrite symMulOf_mono by eauto.
    rewrite Heq2.
    rewrite Heq3.
    reflexivity.

    erewrite symMulOf_mono by eauto.
    rewrite Heq1.
    erewrite symMulOf_mono by eauto.
    rewrite Heq2.
    rewrite Heq3.
    reflexivity.

    repeat erewrite includes_lookup by eauto.
    simplify.
    cases (n2 ==z 0); equality.

    repeat erewrite includes_lookup by eauto.
    simplify.
    cases (n2 ==z 0); equality.

    repeat erewrite includes_lookup by eauto.
    simplify.
    reflexivity.

    repeat erewrite includes_lookup by eauto.
    simplify.
    reflexivity.

    repeat erewrite includes_lookup by eauto.
    simplify.
    reflexivity.

    repeat erewrite includes_lookup by eauto.
    simplify.
    reflexivity.

    eapply VarToNode in Heq0; eauto.
    equality.

    eapply VarToNode in Heq; eauto.
    equality.
  Qed.

  Lemma symInstr_correct : forall i st v0 v nvs,
      compat st v0 v nvs
      -> rhsReads (Rhs i) \subseteq dom st.(Vars)
      -> exists nvs', nvs $<= nvs' /\ compat (symInstr st i) v0 (evalInstr v i) nvs'.
  Proof.
    unfold symInstr, evalInstr; simplify.
    cases (node_kind_in st (kindOfRhs st (Rhs i))).
    specialize (node_kind_in_correct _ _ _ _ (kindOfRhs st (Rhs i)) H).
    rewrite Heq; simplify.
    assert (nodeKindInBounds (NextNode st) (kindOfRhs st (Rhs i))) by eauto.
    propositional.
    invert H3; propositional.
    exists x; propositional.
    constructor; simplify; eauto using InBounds1, OutValsInv.
    cases (x0 ==v Lhs i); subst; simplify; eauto.
    equality.
    cases (x0 ==v Lhs i); subst; simplify; eauto using VarToNodevals.
    invert H5.
    rewrite H6.
    f_equal.
    replace (kindOfRhs st (Rhs i)) with (kindOfRhs s (Rhs i)).
    apply kindOfRhs_correct; auto.
    erewrite node_kind_in_Vars by eauto.
    assumption.
    eapply kindOfRhs_mono; eauto.
    symmetry; eauto.
  Qed.

  Theorem includes_trans : forall A B (m1 m2 m3 : fmap A B),
      m1 $<= m2
      -> m2 $<= m3
      -> m1 $<= m3.
  Proof.
    simplify; apply includes_intro; eauto.
  Qed.

  Lemma symProg_correct : forall pr st v0 v nvs,
      compat st v0 v nvs
      -> progReads pr \subseteq dom (Vars st)
      -> exists nvs', nvs $<= nvs' /\ compat (symProg pr st) v0 (evalProg pr v) nvs'.
  Proof.
    induct pr; simplify; propositional; eauto.

    apply symInstr_correct with (i := a) in H.
    2: cases a; sets.
    invert H; propositional.
    eapply IHpr in H2.
    invert H2; propositional.
    exists x0; propositional; eauto using includes_trans.
    cases (node_kind_in st (kindOfRhs st (Rhs a))); simplify.
    assert (s.(Vars) = st.(Vars)).
    unfold node_kind_in in Heq.
    cases (st.(NodesIn) $? kindOfRhs st (Rhs a)); simplify.
    equality.
    invert Heq.
    reflexivity.
    unfold symInstr.
    rewrite Heq.
    simplify.
    cases a; simplify.
    sets.
    cases (Lhs0 ==v x0); auto.
    right.
    rewrite H1.
    apply H0; propositional.
  Qed.

  Definition initNodevals (v : valuation) : nodeVals :=
    $0 $+ (0, v $! "a") $+ (1, v $! "b") $+ (2, v $! "c").

  Lemma compat_initVars : forall v,
      compat initial v v (initNodevals v).
  Proof.
    unfold initNodevals; constructor; simplify;
      repeat match goal with
             | [ H: Some _ = Some _ |- _ ] => invert H
             | [ |- context[(_ $+ (?x, _)) $? ?y] ] => cases (node_kind_eq_dec x y); subst; simplify
             | [ |- context[(_ $+ (?x, _)) $? ?y] ] => cases (Z.eq_dec x y); subst; simplify
             | [ _ : context[(_ $+ (?x, _)) $? ?y] |- _ ] => cases (Z.eq_dec x y); subst; simplify
             | [ _ : context[(_ $+ (?x, _)) $? ?y] |- _ ] => cases (node_kind_eq_dec x y); subst; simplify
             | [ _ : context[(_ $+ (?x, _)) $? ?y] |- _ ] => cases (string_dec x y); subst; simplify
             end; equality || linear_arithmetic.
  Qed.

  Lemma compat_redoVars : forall st v v' nvs,
      initNodevals v $<= nvs
      -> compat st v v' nvs
      -> compat (redoVars st) v v nvs.
  Proof.
    simplify.
    constructor; simplify; eauto using InBounds1, OutValsInv.
    repeat match goal with
           | [ H: Some _ = Some _ |- _ ] => invert H
           | [ _ : context[(_ $+ (?x, _)) $? ?y] |- _ ] => cases (string_dec x y); subst; simplify
           end;
      unfold initNodevals in *;
      eapply OutValsInv; eauto;
      erewrite includes_lookup; try apply H; simplify; eauto; equality.
    repeat match goal with
           | [ H: Some _ = Some _ |- _ ] => invert H
           | [ _ : context[(_ $+ (?x, _)) $? ?y] |- _ ] => cases (string_dec x y); subst; simplify
           end;
    unfold initNodevals in *;
      erewrite includes_lookup; try apply H; simplify; eauto; equality.
  Qed.

  Local Hint Resolve compat_initVars compat_redoVars : core.

  Theorem equivalent_correct : forall pr1 pr2,
      equivalent pr1 pr2 = true
      -> (progReads pr1 \cup progReads pr2) \subseteq inputs
      -> forall v, evalProg pr1 v $! "out" = evalProg pr2 v $! "out".
  Proof.
    intros.
    unfold equivalent in H.
    repeat match goal with
           | [ H : match ?E with _ => _ end = _ |- _ ] => cases E; try equality
           end.
    assert (exists nvs, initNodevals v $<= nvs /\ compat (symProg pr1 initial) v (evalProg pr1 v) nvs).
    apply symProg_correct; simplify; auto.
    unfold inputs in *; sets; first_order.
    invert H1; propositional.
    assert (exists nvs', x $<= nvs' /\ compat (symProg pr2 (redoVars (symProg pr1 initial))) v (evalProg pr2 v) nvs').
    apply symProg_correct; simplify; eauto.
    generalize H0; clear; sets; first_order.
    invert H2; propositional.
    eapply VarToNodevals in Heq; eauto.
    eapply VarToNodevals in Heq0; eauto.
    apply Z.eqb_eq in H; subst.
    erewrite includes_lookup in Heq0; try apply H2; eauto.
    equality.
  Qed.

End Impl.

Module ImplCorrect : Pset10Sig.S := Impl.

(*|
Authors:

- Adam Chlipala
|*)
