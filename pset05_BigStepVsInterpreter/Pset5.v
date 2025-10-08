(** * 6.512 Formal Reasoning About Programs, Fall 2025 - Pset 5 *)

Require Import Frap.Frap Pset5.Pset5Sig.

Module Impl.
  (* In this pset, we will explore different ways of defining semantics for the
     simple imperative language we used in Chapter 4 (Interpreters.v) and
     Chapter 7 (OperationalSemantics.v).
     Make sure to reread these two files, because many definitions we ask you
     to come up with in this pset are similar to definitions in these two files.

     Pset5Sig.v contains the number of points you get for each definition and
     proof. Note that since we ask you to come up with some definitions
     yourself, all proofs being accepted by Rocq does not necessarily guarantee a
     full score: you also need to make sure that your definitions correspond to
     what we ask for in the instructions. *)

  (* Our language has arithmetic expressions (note that we removed Times and Minus,
     because they don't add anything interesting for this pset): *)
  Inductive arith: Set :=
  | Const (n: nat)
  | Var (x: var)
  | Plus (e1 e2: arith).

  (* And it has commands, some of which contain arithmetic expressions: *)
  Inductive cmd :=
  | Skip
  | Assign (x: var) (e: arith)
  | Sequence (c1 c2: cmd)
  | If (e: arith) (thn els: cmd)
  | While (e: arith) (body: cmd).

  (* As in the lecture, we use a finite map to store the values of variables: *)
  Definition valuation := fmap var nat.

  (** * Part 1: Using a recursive function **)

  (* To make it a bit more interesting, we add a twist:
     If an arithmetic expression reads an undefined variable, instead of just
     returning 0, we specify that an arbitrary value can be returned.
     Therefore, the signature we used in class,

       Fixpoint interp (e: arith) (v: valuation): nat :=
         ...

     will not work any more, because it can only return one value.
     Instead, we will use the following definition: *)

  Fixpoint interp (e: arith) (v: valuation) (retval: nat): Prop :=
    match e with
    | Const n => retval = n
    | Var x =>
      match v $? x with
      | None => True (* any retval is possible! *)
      | Some n => retval = n
      end
    | Plus e1 e2 =>
      exists a1 a2,
      interp e1 v a1 /\
      interp e2 v a2 /\
      retval = a1 + a2
    end.
  (* You can read [interp e v retval] as the claim that "interpreting expression
     e under the valuation v can return the value retval".
     And if we don't provide the last argument, we can think of "interp e v",
     which has type "nat -> Prop", as "the set of all possible values e could
     return". *)

  (* Let's look at some examples: *)

  (* The only result allowed by [Const 3] is [3]: *)
  Compute interp (Const 3) _.

  (* If we interpret the expression "y + z" in a valuation where
     y is 2 and z is 3, then the only possible result is 5. *)

  Goal forall retval,
      interp (Plus (Var "y") (Var "z"))
             ($0 $+ ("y", 2) $+ ("z", 3))
             retval <->
      retval = 5.
  Proof.
    simplify; propositional.
    - cases H; cases H.
      linear_arithmetic.
    - exists 2, 3.
      propositional.
  Qed.

  (* We can also look at this in terms of a partial application: *)

  Goal interp (Plus (Var "y") (Var "z"))
              ($0 $+ ("y", 2) $+ ("z", 3)) =
       (fun retval => retval = 5).
  Proof.
    simplify.
    apply sets_equal; simplify; propositional.
    - cases H; cases H.
      linear_arithmetic.
    - exists 2, 3.
      propositional.
  Qed.

  (* But if we leave [z] unset in the valuation, then [Var "z"] can return any
     value, and hence the complete program can return any value greater than or
     equal to 2. *)
  Goal interp (Plus (Var "y") (Var "z")) ($0 $+ ("y", 2)) = (fun retval => 2 <= retval).
  Proof.
    simplify.
    apply sets_equal.
    propositional.
    - cases H. cases H. linear_arithmetic.
    - exists 2, (x - 2). linear_arithmetic.
  Qed.

  (* Hint that will be useful later:
     In the above proof, you can see how you can deal with existentials:
     - If you have an [H: exists x, P] above the line, you can "cases H"
       to obtain such an "x" and "H: P".
     - If you have an [exists x, P] below the line, you can use "exists x0" to
       provide the value [x0] for which you want to prove the existential.
     Instead of repeating [cases], you can also use [first_order]. *)

  (** * Part 2: Using an inductive relation **)

  (* An alternative way of specifying how arithmetic expressions are evaluated
     is by using inference rules, where we put preconditions above the line,
     the conclusion below the line, and a name of the rule to the right of
     the line, using "Oxford brackets" to write statements of the form
     "a ∈ ⟦e⟧ᵥ" which we read as "the natural number a is in the set of
     values to which e can evaluate under the valuation v".
     If we were to write this on a blackboard, it might look like this:

                           n1 = n2
                        ------------ ValuesConst
                         n1 ∈ ⟦n2⟧ᵥ

                         (x ↦ a) ∈ v
                        -------------- ValuesVarDefined
                           a ∈ ⟦x⟧ᵥ

                         x ∉ dom(v)
                       ------------- ValuesVarUndefined
                         a ∈ ⟦x⟧ᵥ

            a1 ∈ ⟦e1⟧ᵥ   a2 ∈ ⟦e2⟧ᵥ   a=a1+a2
            ----------------------------------- ValuesPlus
                       a ∈ ⟦e1+e2⟧ᵥ

     Let's translate this to an Inductive Prop in Rocq called "values". That is,
     [values e v a] should mean “the natural number a is in the set of
     values to which e can evaluate under the valuation v”.

     Define an Inductive with four constructors, one for each of the four rules
     above, using the names written to the rights of the lines above as the
     constructor names.  We have included ValuesConst to give you a hint.
  *)
  Inductive values: arith -> valuation -> nat -> Prop :=
  | ValuesConst: forall v n1 n2,
      n1 = n2 ->
      values (Const n1) v n2
  | ValuesVarDefined: forall v x a,
      v $? x = Some a ->
      values (Var x) v a
  | ValuesVarUndefined: forall v x a,
      v $? x = None ->
      values (Var x) v a
  | ValuesPlus: forall v a1 e1 a2 e2 a,
      values e1 v a1 ->
      values e2 v a2 ->
      a = a1 + a2 ->
      values (Plus e1 e2) v a
  .

  (* Note that the following alternative would also work for ValuesConst and
     ValuesPlus:

                    ---------- ValuesConst
                     n ∈ ⟦n⟧ᵥ

            a1 ∈ ⟦e1⟧ᵥ     a2 ∈ ⟦e2⟧ᵥ
            --------------------------- ValuesPlus
                a1+a2 ∈ ⟦e1+e2⟧ᵥ

     But in Rocq, this would be a bit less convenient, because the tactic
     [eapply ValuesPlus] would only work if the goal is of the shape
     [values _ _ (_ + _)], whereas if we add this extra equality,
     [eapply ValuesPlus] works no matter what the last argument to [values] is,
     and similarly for [ValuesConst]. *)

  (* Contrary to the Fixpoint-based definition "interp", we can't do simplification
     of the kind "replace interp by its body and substitute the arguments in it",
     because an Inductive Prop describes a family of proof trees and isn't a
     function with a right-hand side you could plug in somewhere else.
     In order to prove the example Goal from above for "values", we need to construct
     the following proof tree:

    ("y"↦2) ∈ {"y"↦2}              "z" ∉ dom({"y"↦2})
   -------------------- Defined    ----------------------- Undefined
    2 ∈ ⟦"y"⟧_{"y"↦2}               a-2 ∈ ⟦"z"⟧_{"y"↦2}              a=2+a-2
   ---------------------------------------------------------------------------- ValuesPlus
                        a ∈ ⟦"y"+"z"⟧_{"y"↦2}
  *)
  Example values_example: forall a,
      2 <= a ->
      values (Plus (Var "y") (Var "z")) ($0 $+ ("y", 2)) a.
  Proof.
    (* "simplify" only introduces the hypotheses but can't really simplify
       anything here. This is not a limitation of "simplify"; it's due to the
       way [values] is defined. *)
    simplify.
    (* Once you define the four constructors for "values", you can uncomment
       the script below. Make sure you understand how it relates to the proof
       tree above! *)

    eapply ValuesPlus with (a1 := 2) (a2 := a - 2).
    - eapply ValuesVarDefined. simplify. equality.
    - eapply ValuesVarUndefined. simplify. equality.
    - linear_arithmetic.

  Qed.

  (* Now, let's prove that "interp" and "values" are equivalent.
     First, [interp -> values]: *)
  Theorem interp_to_values: forall e v a,
      interp e v a -> values e v a.
  Proof.
      induct e.
      simplify.
      apply ValuesConst with (v:= v) (n1 := n)(n2:= a); linear_arithmetic.

      simplify.
      cases (v $? x).
      -invert H. eapply ValuesVarDefined; assumption.
      - simplify. eapply ValuesVarUndefined; assumption.
      - simplify. cases H; cases H.
        propositional.
        apply IHe1 in H0.
        apply IHe2 in H.
        eapply ValuesPlus.
        apply H0.
        apply H.
        apply H2.
  Qed.

  (* To prove the other direction, we have a choice: we can either induct on
     [e] or directly on the proof of [values e v a], because [values] is an
     inductively defined predicate.

     Let's do both proofs.  In general, inducting on the proof tree is the right
     approach, so let's start with that: *)
  Theorem values_to_interp: forall e v a,
      values e v a -> interp e v a.
  Proof.
    induct 1; (* ← do not change this line *)
      simplify.
      - linear_arithmetic.
      - cases (v $? x).
        invert H; linear_arithmetic.
        linear_arithmetic.
      - cases (v $? x).
        invert H.
        linear_arithmetic.
      - exists a1, a2.
        propositional.
  Qed.

  (* Now let's see how things look with an induction on e.  In this simple case,
     it's very similar: *)
  Theorem values_to_interp_induction_on_e: forall e v a,
      values e v a -> interp e v a.
  Proof.
    induct e; (* ← not the best, but for the sake of the exercise do not change this line *)
      simplify.
      - invert H. equality.
      - invert H. cases (v $? x).
        invert H1. equality.
        linear_arithmetic.

        cases (v $? x).
        invert H1.
        linear_arithmetic.
      - invert H. exists a1, a2.
        propositional.
        apply IHe1; assumption.
        apply IHe2; assumption.
  Qed.

  (* Let's define nondeterministic big-step semantics for evaluating a command.
     Define [eval] as an Inductive Prop such that [eval v1 c v2] means
     "If we run command c on valuation v1, we can obtain valuation v2".
     Whenever you encounter an arithmetic expression, use [values] to obtain a
     value it can step to.
     Hint: This will be quite similar to [eval] in OperationalSemantics.v! *)
  Inductive eval: valuation -> cmd -> valuation -> Prop :=
  | EvalSkip: forall v,
      eval v Skip v
  | EvalAssign: forall v x e a,
      values e v a
      -> eval v (Assign x e) (v $+ (x, a))
  | EvalSeq: forall v c1 v1 c2 v2,
      eval v c1 v1
      -> eval v1 c2 v2
      -> eval v (Sequence c1 c2) v2
  | EvalIfTrue: forall v e thn els v' a,
      values e v a
      -> a <> 0
      -> eval v thn v'
      -> eval v (If e thn els) v'
  | EvalIfFalse: forall v e thn els v' a,
      values e v a
      -> a = 0
      -> eval v els v'
      -> eval v (If e thn els) v'
  | EvalWhileTrue: forall v e body v' v'' a,
      values e v a ->
      a <> 0
      -> eval v body v'
      -> eval v' (While e body) v''
      -> eval v (While e body) v''
  | EvalWhileFalse: forall v e body a,
      values e v a
      -> a = 0
      -> eval v (While e body) v
  .

  (* Hint: Many of the proofs below will depend on definitions we ask you to
     find yourself, and if you get these definitions wrong, the proofs will
     not work, so keep in mind that you might have to go back and adapt your
     definitions!
     Also, it can happen that many proofs go through and you become (overly)
     confident that your definitions are correct, even though they aren't. *)

  (* Here's an example program. If we run it on the empty valuation, reading the
     variable "oops" can return any value, but after that, no matter whether
     "oops" was zero or not, we assign a nonzero value to "tmp", so the answer
     will always be 42. *)
  Example the_answer_is_42 :=
    Sequence (Assign "x" (Var "oops"))
             (Sequence (If (Var "x")
                           (Assign "tmp" (Plus (Var "x") (Var "x")))
                           (Assign "tmp" (Const 1)))
                       (If (Var "tmp")
                           (Assign "answer" (Const 42))
                           (Assign "answer" (Const 24)))).

  (* To prove that this sample program always returns 42, we first prove a handy
     helper lemma (the [simplify] tactic will help with [$+]): *)
  Lemma read_last_value: forall x v c n,
      values (Var x) (v $+ (x, c)) n -> n = c.
  Proof.
      simplify.
      invert H. simplify.
      invert H1; equality.

      simplify. invert H1; equality.
  Qed.

  (* Hint: This next theorem is a bit boring -- it's about 30 lines of "invert",
     "simplify", "discriminate", "equality", "linear_arithmetic" and
     "apply read_last_value in H", "subst" in our solution.

     But it's a good test case to make sure you got the definition of "eval"
     right! And note that inverting the hypotheses in the right order, i.e. in
     the order the program is executed, as well as using "read_last_value"
     whenever possible, will make your proof less long.

     (Or, you could use automation — our automated proof is 8 lines long.) *)
  Theorem the_answer_is_indeed_42:
    forall v, eval $0 the_answer_is_42 v -> v $? "answer" = Some 42.
  Proof.
      simplify.
      invert H.
      invert H3.
      invert H5.
      invert H2.
      invert H6.
      apply read_last_value in H5.
      subst.
      invert H9.
      apply read_last_value in H3.
      subst.
      invert H11.
      invert H3.
      simplify. equality.

      invert H9.
      apply read_last_value in H5.
      subst.
      invert H11.
      apply read_last_value in H3.
      subst.
      simplify.
      invert H6.
      invert H5.
      apply read_last_value in H1; subst.
      apply read_last_value in H2; subst.
      linear_arithmetic.

      invert H9.
      invert H6.
      invert H10.
      simplify.
      apply read_last_value in H5; subst.
      apply read_last_value in H7; subst.
      invert H6. equality.

      invert H10.
      apply read_last_value in H7.
      apply read_last_value in H5.
      subst.
      simplify.
      invert H6. invert H3.
      discriminate.
  Qed.

  (* Here's another example program. If we run it on a valuation that is
     undefined for "x", it will read the undefined variable "x" to decide
     whether to abort the loop, so any number of loop iterations is possible. *)
  Example loop_of_unknown_length :=
    (While (Var "x") (Assign "counter" (Plus (Var "counter") (Const 1)))).

  (* Hint: you might need the "maps_equal" tactic to prove that two maps are the same. *)
  Theorem eval_loop_of_unknown_length: forall n initialCounter,
      eval ($0 $+ ("counter", initialCounter))
           loop_of_unknown_length
           ($0 $+ ("counter", initialCounter + n)).
  Proof.
    unfold loop_of_unknown_length.
    induct n; simplify.
    - rewrite Nat.add_0_r.
      eapply EvalWhileFalse.
      eapply ValuesVarUndefined. simplify. equality.
      equality.
    - eapply EvalWhileTrue with (a:=1).
      apply ValuesVarUndefined. simplify. equality.
      equality.
      eapply EvalAssign.
      apply ValuesPlus with (a1 := initialCounter) (a2 := 1).
      apply ValuesVarDefined. simplify. equality.
      apply ValuesConst. linear_arithmetic.
      reflexivity.
      assert ($0 $+ ("counter", initialCounter) $+ ("counter", initialCounter + 1) =
              $0 $+ ("counter", initialCounter + 1)) by (maps_equal).
      rewrite H.
      replace (initialCounter + S n) with (initialCounter + 1 + n) by linear_arithmetic.
      apply IHn.
  Qed.

  (* Wherever this TODO_FILL_IN is used, you should replace it with your own code. *)
  Axiom TODO_FILL_IN: Prop.

  (** * Part 3: Fixpoints with fuel **)

  (* You might wonder whether we can use "Fixpoint" instead of "Inductive" to define
     such nondeterministic big-step evaluation of commands, and indeed we can.
     But we need some trick to convince Rocq that this Fixpoint will always terminate,
     even though there could be infinite loops.

     We achieve this by using a "fuel" argument that limits the recursion depth.
     This does not exclude any possible final valuations, because for every final
     valuation, there exists a recursion depth sufficient to reach it.

     So let's define a Fixpoint [run] such that [run fuel v1 c v2] means
     "if we run command c on valuation v1 and limit the recursion depth to fuel,
     we can obtain valuation v2".

     We already defined all cases for you except the [While] case, but all the
     building blocks you need can be found in the other cases, too.
   *)
  Fixpoint run (fuel: nat) (v1: valuation) (c: cmd) (v2: valuation): Prop :=
    match fuel with
    | O => False
    | S fuel' =>
      match c with
      | Skip => v1 = v2
      | Assign x e => exists a, interp e v1 a /\ v2 = (v1 $+ (x, a))
      | Sequence c1 c2 => exists vmid, run fuel' v1 c1 vmid /\ run fuel' vmid c2 v2
      | If e c1 c2 =>
        (exists r, interp e v1 r /\ r <> 0 /\ run fuel' v1 c1 v2) \/
        (interp e v1 0 /\ run fuel' v1 c2 v2)
      | While e c1 =>
        (* TODO_FILL_IN *)
        exists r vmid, (interp e v1 r /\ r = 0 /\ v1 = v2) \/ (interp e v1 r /\ r <> 0 /\ run fuel' v1 c1 vmid /\ run fuel' vmid (While e c1) v2)
      end
    end.

  (* Now let's prove that [run] and [eval] are equivalent! *)

  Local Hint Constructors eval : core.

  Theorem run_to_eval: forall fuel v1 c v2,
      run fuel v1 c v2 ->
      eval v1 c v2.
  Proof.
   induct fuel; simplify.
   cases c.
   exfalso. assumption.
   exfalso. assumption.
   exfalso. assumption.
   exfalso. assumption.
   exfalso. assumption.

   cases c.
   invert H; apply EvalSkip.
   cases H; cases H.
   invert H0.
   apply EvalAssign.
   apply interp_to_values in H; assumption.

   cases H; cases H.
   simplify.
   apply IHfuel in H, H0.
   pose (EvalSeq _ _ _ _ _ H H0).
   assumption.

   cases H; cases H.
   propositional.
   apply IHfuel in H2.
   apply interp_to_values in H0.
   pose (EvalIfTrue _ _ c1 c2 _ _ H0 H H2).
   assumption.

   apply IHfuel in H0.
   apply interp_to_values in H.
   assert (0 = 0) by linear_arithmetic.
   pose (EvalIfFalse _ _ c1 c2 _ _ H H1 H0).
   assumption.

   cases H; cases H.
   propositional.
   apply interp_to_values in H.
   pose (EvalWhileFalse _ _ c _ H H0).
   invert H2.
   assumption.

   apply IHfuel in H1, H3.
   apply interp_to_values in H.
   pose (EvalWhileTrue _ _ _ _ _ _ H H0 H1 H3).
   assumption.
  Qed.

  (* To prove the other direction, we will need the following lemma, which shows
     that excess fuel isn't an issue.

     Hint: Here, some proof automation might pay off!

     You could try writing a [repeat match goal] loop, to do all possible
     simplifications on your hypotheses and then use [eauto] to solve
     the goal. Maybe you need to increase the maximum search depth of eauto;
     in our solution, we had to write [eauto 9] instead of just [eauto],
     which defaults to [eauto 5].

     Some useful documentation pointers:
     - https://rocq-prover.org/doc/V9.0.0/refman/proofs/automatic-tactics/auto.html#coq:tacn.eauto
     - https://rocq-prover.org/doc/V9.0.0/refman/proof-engine/ltac.html#pattern-matching-on-goals-and-hypotheses-match-goal

     And note that [eauto] does not know about linear arithmetic by default,
     so you could consider registering it as a [Hint Extern], but a simpler
     way here would be to use the lemma "le_S_n" to turn "S fuel1 <= S fuel2"
     into "fuel1 <= fuel2", which will be needed for the IH. *)

  Lemma run_monotone: forall fuel1 fuel2 v1 c v2,
      fuel1 <= fuel2 ->
      run fuel1 v1 c v2 ->
      run fuel2 v1 c v2.
  Proof.
    induct fuel1; simplify.
    exfalso. assumption.

    destruct fuel2.
    invert H.
    simplify.
    cases c.
    assumption.

    cases H0; propositional.
    exists x0; propositional.

    cases H0; propositional.
    exists x; propositional.
    apply le_S_n in H.
    apply IHfuel1; assumption.
    apply le_S_n in H.
    apply IHfuel1. assumption.
    assumption.

    cases H0; propositional.
    cases H0; propositional.
    apply le_S_n in H.
    left. exists x.
    propositional.
    apply IHfuel1 with (fuel2:=fuel2) in H3; assumption.

    apply le_S_n in H.
    right. propositional.
    apply IHfuel1 with (fuel2:=fuel2) in H2; assumption.

    cases H0; propositional.
    cases H0; propositional.
    apply le_S_n in H.
    exists x.
    exists v2.
    propositional.

    apply le_S_n in H.
    exists x.
    exists x0.
    right. propositional.
    apply IHfuel1 with (fuel2:=fuel2) in H2; assumption.
    apply IHfuel1 with (fuel2:=fuel2) in H4; assumption.
  Qed.

  (* For the other direction, we could naively start proving it like this: *)
  Theorem eval_to_run: forall v1 c v2,
      eval v1 c v2 -> exists fuel, run fuel v1 c v2.
  Proof.
    induct 1; simplify.
    (* This proof is relatively short and straightforward, but dealing with
       existentials is not very pleasant!

       This problem becomes worse if we make many proofs about "run".  So, instead,
       let's look at a nicer formulation of this theorem. *)
  Abort. (* <-- do not change this line *)


  (* We will first define a wrapper around "run" that hides the existential: *)
  Definition wrun (v1: valuation) (c: cmd) (v2: valuation): Prop :=
    exists fuel, run fuel v1 c v2.

  (* The idea is that in the run_to_eval proof above, using the constructors of
     "eval", i.e. doing "eapply EvalAssign", "eapply EvalSeq", "eapply EvalIfTrue",
     was quite convenient, so let's expose the same "API" for constructing proofs
     of "run" (or actually, proofs of the slightly nicer "wrun"). *)

  (* Now let's define proof rules to get the same "API" for "wrun" as for "eval".
     Hint: Again, some proof automation might simplify the task (but manual proofs are
     possible too, of course).  You may find the `max` function useful. *)

  Definition WRunSkip_statement : Prop :=
    forall v,
      wrun v Skip v.
  Lemma WRunSkip: WRunSkip_statement.
  Proof.
    unfold WRunSkip_statement; simplify.
    unfold wrun.
    exists 1.
    simplify.
    equality.
  Qed.

  Definition WRunAssign_statement : Prop :=
    forall v x e a,
      interp e v a ->
      wrun v (Assign x e) (v $+ (x, a)).
  Lemma WRunAssign: WRunAssign_statement.
  Proof.
    unfold WRunAssign_statement; simplify.
    unfold wrun.
    exists 1.
    simplify.
    exists a.
    propositional.
  Qed.

  Definition WRunSeq_statement : Prop :=
    forall v c1 v1 c2 v2,
      wrun v c1 v1 ->
      wrun v1 c2 v2 ->
      wrun v (Sequence c1 c2) v2.
  Lemma WRunSeq: WRunSeq_statement.
  Proof.
    unfold WRunSeq_statement; simplify.
    unfold wrun in *.
    cases H; cases H0.
    exists (S (max x0 x)).
    simplify.
    propositional.
    apply run_monotone with (fuel2 := max x0 x) in H, H0.
    exists v1; propositional.
    linear_arithmetic.
    linear_arithmetic.
  Qed.

  (* For the next few lemmas, we've left you the job of stating the theorem as
     well as proving it. *)

  Definition WRunIfTrue_statement : Prop :=
    forall v e c1 c2 v' r,
      interp e v r ->
      r <> 0 ->
      wrun v c1 v' ->
      wrun v (If e c1 c2) v'.
  Lemma WRunIfTrue: WRunIfTrue_statement.
  Proof.
    simplify.
    unfold WRunIfTrue_statement.
    simplify.
    unfold wrun.
    unfold wrun in H1.
    cases H1.
    exists (S x).
    simplify.
    left. exists r.
    propositional.
  Qed.

  Definition WRunIfFalse_statement : Prop :=
    forall v e c1 c2 v',
      interp e v 0 ->
      wrun v c2 v' ->
      wrun v (If e c1 c2) v'.
  Lemma WRunIfFalse: WRunIfFalse_statement.
  Proof.
    simplify.
    unfold WRunIfFalse_statement.
    simplify.
    unfold wrun.
    unfold wrun in H0.
    cases H0.
    exists (S x).
    simplify.
    right.
    propositional.
  Qed.

  Definition WRunWhileTrue_statement : Prop :=
    forall v e body v' v'' r,
      interp e v r ->
      r <> 0 ->
      wrun v body v' ->
      wrun v' (While e body) v'' ->
      wrun v (While e body) v''.
  Lemma WRunWhileTrue: WRunWhileTrue_statement.
  Proof.
    simplify.
    unfold WRunWhileTrue_statement.
    simplify.
    unfold wrun.
    unfold wrun in H1, H2.
    cases H1; cases H2.
    exists (S (max x0 x)).
    apply run_monotone with (fuel2:=(max x0 x)) in H1, H2.
    simplify.
    exists r.
    exists v'.
    right. propositional.
    linear_arithmetic.
    linear_arithmetic.
  Qed.

  Definition WRunWhileFalse_statement : Prop :=
    forall v e body r,
      interp e v r ->
      r = 0 ->
      wrun v (While e body) v.
  Lemma WRunWhileFalse: WRunWhileFalse_statement.
  Proof.
    simplify.
    unfold WRunWhileFalse_statement.
    simplify.
    unfold wrun.
    exists 1.
    simplify.
    exists r.
    exists v.
    propositional.
  Qed.

  (* Now, thanks to these helper lemmas, proving the direction from eval to wrun
     becomes easy: *)
  Theorem eval_to_wrun: forall v1 c v2,
      eval v1 c v2 ->
      wrun v1 c v2.
  Proof.
    induct 1; simplify.
    apply WRunSkip.
    apply WRunAssign.
    apply values_to_interp.
    assumption.

    eapply WRunSeq.
    apply IHeval1.
    assumption.

    eapply WRunIfTrue.
    apply values_to_interp in H.
    apply H.
    assumption.
    assumption.

    eapply WRunIfFalse.
    apply values_to_interp in H.
    invert H0.
    assumption.
    assumption.

    eapply WRunWhileTrue.
    apply values_to_interp in H.
    apply H.
    assumption.
    apply IHeval1.
    assumption.

    eapply WRunWhileFalse.
    apply values_to_interp in H.
    apply H.
    apply H0.
  Qed.

  (* Remember when we said earlier that [induct 1] does induction on the proof
     of [eval], whereas [induct c] does induction on the program itself?  Try
     proving the above with [induct c] instead of [induct 1], skipping straight
     to the [While] cases.  Why isn't the theorem provable this way? *)

  (* The following definitions are needed because of a limitation of Rocq
     (the kernel does not recognize that a parameter can be instantiated by an
     inductive type).
     Please do not remove them! *)
  Definition values_alias_for_grading := values.
  Definition eval_alias_for_grading := eval.

  (* You've reached the end of this pset, congratulations! *)

  (* ****** Everything below this line is optional ****** *)

  (* Many of the proofs above can be automated.  A good way to test your
     automation is to make small changes to the language.

     For example, you could add an [Unset: string -> cmd] constructor to the
     definition of [cmd]; the semantics of that command should be to remove a
     variable from the current valuation (use [v $- "x"] to remove ["x"] from
     [v]).

     In our solution, adding [Unset] and updating definitions and proofs
     accordingly takes just a few extra lines.  Try it in yours! *)

  (* Let's take the deterministic semantics we used in OperationalSemantics.v but
     prefix them with "d" to mark them as deterministic: *)

  Fixpoint dinterp (e: arith) (v: valuation): nat :=
    match e with
    | Const n => n
    | Var x =>
      match v $? x with
      | None => 0
      | Some n => n
      end
    | Plus e1 e2 => dinterp e1 v + dinterp e2 v
    end.

  Inductive deval: valuation -> cmd -> valuation -> Prop :=
  | DEvalSkip: forall v,
      deval v Skip v
  | DEvalAssign: forall v x e,
      deval v (Assign x e) (v $+ (x, dinterp e v))
  | DEvalSeq: forall v c1 v1 c2 v2,
      deval v c1 v1 ->
      deval v1 c2 v2 ->
      deval v (Sequence c1 c2) v2
  | DEvalIfTrue: forall v e thn els v',
      dinterp e v <> 0 ->
      deval v thn v' ->
      deval v (If e thn els) v'
  | DEvalIfFalse: forall v e thn els v',
      dinterp e v = 0 ->
      deval v els v' ->
      deval v (If e thn els) v'
  | DEvalWhileTrue: forall v e body v' v'',
      dinterp e v <> 0 ->
      deval v body v' ->
      deval v' (While e body) v'' ->
      deval v (While e body) v''
  | DEvalWhileFalse: forall v e body,
      dinterp e v = 0 ->
      deval v (While e body) v.

  (* Now let's prove that if a program evaluates to a valuation according to the
     deterministic semantics, it also evaluates to that valuation according to
     the nondeterministic semantics (the other direction does not hold, though). *)
  Theorem deval_to_eval: forall v1 v2 c,
      deval v1 c v2 ->
      eval v1 c v2.
  Proof.
  Admitted.

  (* In deterministic semantics, Fixpoints work a bit better, because they
     can return just one value, and let's use "option" to indicate whether
     we ran out of fuel: *)
  Fixpoint drun(fuel: nat) (v: valuation) (c: cmd): option valuation. Admitted.

  (* More open-ended exercise:
     Now we have six different definitions of semantics:

                          deterministic     nondeterministic

     Inductive            deval             eval

     Wrapped Fixpoint     dwrun             wrun

     Fixpoint             drun              run

     We have proved that all the nondeterministic semantics are equivalent among
     each other.
     If you want, you could also prove that all the deterministic semantics are
     equivalent among each other and experiment whether it's worth creating an
     "Inductive"-like API for "dwrun", or whether you're ok dealing with drun's
     existentials when proving deval_to_drun.
     Moreover, we have proved that "deval" implies "eval", so every definition in
     the left column of the above table implies every definition in the right
     column of the table.
     If you're curious to learn more about the trade-offs between Inductive Props
     and Fixpoints, you can try to prove some of these implications directly
     and see how much harder than "deval_to_eval" it is (we believe that
     "deval_to_eval" is the simplest one).
   *)

End Impl.

Module ImplCorrect : Pset5Sig.S := Impl.

(* Authors:
   Samuel Gruetter
   Clément Pit-Claudel *)
