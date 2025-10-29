(*|
==========================================================
 6.512 Formal Reasoning About Programs, Fall 2025 - Pset 8
==========================================================
|*)

Require Import Pset8.Pset8Sig.

(*|
Introduction
============

Computer programs commonly manipulate data from different sources, at different
levels of privacy or trust. An e-commerce website, for example, might keep track
of the contents of each individual cart, and it would be a severe issue if one user
got access to the content of another user's cart.

Such “information-flow” issues are of a different nature from the functionality bugs
that we usually think of, but they are also pervasive and tricky to detect and fix:
for example, for a few weeks in 2011, Facebook's abuse-reporting tool made it possible
to access a user's private photos by reporting one of their *public* photos for abuse:
the tool would then conveniently offer to report other photos, *including private ones*
that the reporter was not allowed to access.
(https://www.zdnet.com/article/facebook-flaw-allows-access-to-private-photos/)

In this pset, we will see how type systems can help with information-flow issues.
We will operate in a simplified setting in which all information is either
“public” or “private”, and we will concern ourselves only with *confidentiality*,
the property that private inputs should not influence public program outputs.

Informally, we'll prove the correctness of a type system such that type-safe programs
do not leak private data: that is, we'll prove that changing the private inputs of
a well-typed program does not change its public outputs. We'll say that well-typed
programs are “confidential”.

Note that this formulation doesn't rule out side channels: changing the private inputs
of a program might change its runtime or even whether it terminates.

Language definition
===================

This is as usual:
|*)

Module Impl.
Inductive bop := Plus | Minus | Times.

Inductive arith : Set :=
| Const (n : nat)
| Var (x : var)
| Bop (b : bop) (e1 e2 : arith).

Coercion Const : nat >-> arith.
Coercion Var : var >-> arith.
Declare Scope  arith_scope.
Notation "a + b" := (Bop Plus a b) : arith_scope.
Notation "a - b" := (Bop Minus a b) : arith_scope.
Notation "a * b" := (Bop Times a b) : arith_scope.
Delimit Scope arith_scope with arith.

Inductive cmd :=
| Skip
| Assign (x : var) (e : arith)
| Sequence (c1 c2 : cmd)
| If (e : arith) (thn els : cmd)
| While (e : arith) (body : cmd).

(* Here are some notations for the language, which again we won't really explain. *)
Notation "x <- e" := (Assign x e%arith) (at level 75).
Infix ";;" := Sequence (at level 76). (* This one changed slightly, to avoid parsing clashes. *)
Notation "'when' e 'then' thn 'else' els 'done'" := (If e%arith thn els) (at level 75, e at level 0).
Notation "'while' e 'loop' body 'done'" := (While e%arith body) (at level 75).

(*|
Program semantics
=================

And the semantics of the language are as expected; the language is made deterministic
by defaulting to 0 when a variable is undefined.
|*)

Definition valuation := fmap var nat.

Fixpoint interp (e : arith) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x =>
    match v $? x with
    | None => 0
    | Some n => n
    end
  | Bop bp e1 e2 =>
    match bp with
    | Plus => Nat.add
    | Minus => Nat.sub
    | Times => Nat.mul
    end (interp e1 v) (interp e2 v)
  end.

Inductive eval : valuation -> cmd -> valuation -> Prop :=
| EvalSkip : forall v,
    eval v Skip v
| EvalAssign : forall v x e,
    eval v (Assign x e) (v $+ (x, interp e v))
| EvalSeq : forall v c1 v1 c2 v2,
    eval v c1 v1
    -> eval v1 c2 v2
    -> eval v (Sequence c1 c2) v2
| EvalIfTrue : forall v e thn els v',
    interp e v <> 0
    -> eval v thn v'
    -> eval v (If e thn els) v'
| EvalIfFalse : forall v e thn els v',
    interp e v = 0
    -> eval v els v'
    -> eval v (If e thn els) v'
| EvalWhileTrue : forall v e body v' v'',
    interp e v <> 0
    -> eval v body v'
    -> eval v' (While e body) v''
    -> eval v (While e body) v''
| EvalWhileFalse : forall v e body,
    interp e v = 0
    -> eval v (While e body) v.

(*|
Typing judgment
===============

The `Confidential` judgment below indicates that a program respects confidentiality.
It takes a set of public variables and a command and returns a `Prop` indicating whether
the program is safe. Take the time to understand exactly how `Confidential` works
(or, even better, take a few moments to think about how you would define a `Confidential` predicate).

In full generality, an information-flow system associates a label to each variable.
We'll simplify things and classify variables as “public” or “private”, and instead of
having a map giving the label of each value, we'll keep track of the set of all public variables.

First, we need a way to collect the variables of an expression
(We haven't seen the `set` type too often; see the tips in ``Pset8Sig.v`` for a quick recap).
|*)

Fixpoint vars (e: arith) : set var :=
  match e with
  | Const n => {} (** A constant has no variables **)
  | Var x => {x} (** A variable has… one variable! **)
  | Bop _ e1 e2 => vars e1 \cup vars e2 (** An operator's variables are the variables of its subterms **)
  end.

(*|
The parameter `pub` below represents the set of all public variables.
This is predeclared and fixed. But there is also a distinct `set var` argument.
This is because we need to consider *implicit* as well as *explicit* flows.

- An explicit flow happens when assigning to a variable.
  If `e` mentions variable `x`, then `y := e` may cause data to flow from `x` into `y`.
  If `x` is private and `y` is public, we want to rule that out.

- An implicit flow happens when assigning to a variable *under a conditional*.
  If `e` mentions variable `x`, then `when e then y := 1` may cause data to flow
  from `x` to `y` (can you see why?). There, too, if `x` is private and `y` is public,
  we want to disallow this flow.

This is why we have the second `set var` (`cv`) argument below:
In addition to the set of public variables, we keep track of the set of variables
from which data may flow implicitly via their effect on control flow.
We call that set “cv”, for “control variables”.
|*)

Inductive Confidential (pub: set var) : set var (* cv *) -> cmd (* program *) -> Prop :=
| ConfidentialSkip : forall cv,
    Confidential pub cv Skip
(** A `Skip` is safe. **)
| ConfidentialAssignPrivate : forall cv x e,
    ~ x \in pub ->
    Confidential pub cv (Assign x e)
(** Assigning to a private variable is safe. **)
| ConfidentialAssignPublic : forall cv x e,
    vars e \subseteq pub ->
    cv \subseteq pub ->
    Confidential pub cv (Assign x e)
(** Assigning to a public variable variable is safe as long as
    the expression does not mention private variables and
    we are not under a conditional that depends on private variables. **)
| ConfidentialSeq : forall cv c1 c2,
    Confidential pub cv c1 ->
    Confidential pub cv c2 ->
    Confidential pub cv (Sequence c1 c2)
(** A sequence is safe if both halves of it are safe. **)
| ConfidentialIf : forall cv e thn els,
    Confidential pub (cv \cup vars e) thn ->
    Confidential pub (cv \cup vars e) els ->
    Confidential pub cv (If e thn els)
(** A conditional is safe if both branches are safe,
    noting that the branches run with additional variables in the `cv`. **)
| ConfidentialWhile : forall cv e body,
    Confidential pub (cv \cup vars e) body ->
    Confidential pub cv (While e body).
(** A while loop is safe if its body is safe,
    noting that the body runs with additional variables in the `cv`. **)

(*|
Here are a few examples:
|*)

Definition pub_example := {"x", "y", "z"}. (* Variables x, y, z are public. *)

Example confidential_prog :=
  ("x" <- "y" + 1;;
   "a" <- "a" * "b";;
   when "y" then "a" <- 0 else "b" <- 0 done).

Goal Confidential pub_example {} confidential_prog.
Proof.
  unfold confidential_prog, pub_example.
  apply ConfidentialSeq; simplify.
  - apply ConfidentialSeq; simplify.
    + apply ConfidentialAssignPublic; simplify.
      * sets.
      * sets.
    + apply ConfidentialAssignPrivate; simplify.
      sets.
  - apply ConfidentialIf; simplify.
    + apply ConfidentialAssignPrivate; simplify.
      sets.
    + apply ConfidentialAssignPrivate; simplify.
      sets.
Qed.

Example leaky_prog :=
  (when "a" then "x" <- 1 else "x" <- 2 done).

Goal ~ Confidential pub_example {} leaky_prog.
Proof.
  unfold leaky_prog, pub_example, not; simplify.
  invert H; simplify.
  invert H3; simplify.
  - sets.
  - pose proof @subseteq_In _ "a" _ _ H4.
    sets.
Qed.

(*|
Proof of noninterference
=========================

We first need a relation to characterize “equivalent” valuations — that is,
valuations that agree on all public variables.
`restrict s m` means restrict the valuation `m` to just the keys in `s`:
|*)

Definition same_public_state pub (v1 v2: valuation) :=
  restrict pub v1 = restrict pub v2.

(* Before we get started proving properties of our type system, please read
   Pset8Sig.v and consider the questions below. The only graded question is
   the multiple-choice one, but we are assigning the rest in hopes that they
   help you complete the following parts.

 Suppose an expression contains only public variables. Under what valuations
 do we expect them to evaluate to the same value?



 Suppose an expression evaluates to different values under different
 valuations. What do we know about this expression if the different valuations
 share the same public state? Do we know anything if the valuations do not
 share the same public state?



 The noninterference property says that running a program in states with
 private variables holding potentially different values does not change the
 public outputs of the program.

 The key difficulty is to deal with *divergence* — the cases where the two
 program executions take different paths.

 When does this happen?  How does that translate in terms of the variables
 in `cv`?

 Can a divergent execution affect the values of public variables?



 When a Confidential program executes, in what ways can it modify the
 valuation? How does this depend on the values of `cv`?


 Finally, can the value of a private variable (one not in `pub`) determine
 whether a confidential program terminates? Assign the definition below to
 `true` if so, and `false` if not.

 *)

Definition private_can_determine_termination := true.

Lemma restrict_add_not_in :
  forall (s : set var) (v : valuation) (x : var) (n : nat),
    ~ x \in s ->
    restrict s (v $+ (x, n)) = restrict s v.
Proof.
  intros.
  apply fmap_ext.
  intros y.
  excluded_middle (y \in s).
  - rewrite lookup_restrict_true by assumption.
    rewrite lookup_restrict_true by assumption.
    rewrite lookup_add_ne.
    + reflexivity.
    + intro Heq.
      subst.
      sets.
  - rewrite lookup_restrict_false by (sets; assumption).
    rewrite lookup_restrict_false by (sets; assumption).
    trivial.
Qed.


Lemma restrict_add_in :
  forall (s : set var) (v : valuation) (x : var) (n : nat),
    x \in s ->
    restrict s (v $+ (x, n)) = (restrict s v) $+ (x, n).
Proof.
  intros.
  apply fmap_ext.
  intros y.
  excluded_middle (y \in s).
  - rewrite lookup_restrict_true by assumption.
    cases (y ==v x).
    + rewrite !lookup_add_eq; eauto.
    + rewrite lookup_add_ne by assumption.
      rewrite lookup_add_ne by assumption.
      rewrite lookup_restrict_true by assumption.
      reflexivity.
  - rewrite lookup_restrict_false by (sets; assumption).
    simplify.
    rewrite lookup_restrict_false by (sets; assumption).
    trivial.
Qed.

Lemma interp_eq_when_vars_in :
  forall (S : set var) (e : arith) (v1 v2 : valuation),
    vars e \subseteq S ->
    restrict S v1 = restrict S v2 ->
    interp e v1 = interp e v2.
Proof.
  intros S e.
  induct e; simplify; intros.
  - trivial.
  - simplify.
    assert (x \in S) by (simplify; sets).
    specialize (f_equal (fun m => m $? x) H0).
    simplify.
    assert (v1 $? x = v2 $? x) as Heq.
    {
      rewrite lookup_restrict_true in H2 by assumption.
      rewrite lookup_restrict_true in H2 by assumption.
      assumption.
    }
    rewrite Heq.
    trivial.
  - assert (vars e1 \subseteq S) by (simplify; sets).
    assert (vars e2 \subseteq S) by (simplify; sets).
    pose proof (IHe1 v1 v2 H1 H0).
    pose proof (IHe2 v1 v2 H2 H0).
    rewrite H3.
    rewrite H4.
    trivial.
Qed.

Lemma confidential_mono_dumb:
  forall cmd pub cv1,
    Confidential pub cv1 cmd ->
  forall cv2,
    cv2 \subseteq cv1 ->
    Confidential pub cv2 cmd.
Proof.
  simplify; induct H; eauto.
  - eapply ConfidentialSkip; eauto; sets.
  - eapply ConfidentialAssignPrivate; eauto; sets.
  - eapply ConfidentialAssignPublic; eauto; sets.
  - eapply ConfidentialSeq; eauto; sets.
  - eapply ConfidentialIf; eauto; sets.
    eapply IHConfidential1; eauto; sets.
    eapply IHConfidential2; eauto; sets.
  - eapply ConfidentialWhile; eauto; sets.
    eapply IHConfidential; eauto; sets.
Qed.


Lemma restrict_unaffected :
  forall (v v' : valuation) (c : cmd) (pub cv : set var),
    eval v c v' ->
    Confidential pub cv c ->
    ~ cv \subseteq pub ->
    restrict pub v' = restrict pub v.
Proof.
  simplify; induct H; eauto.

  invert H0; eauto.
  rewrite restrict_add_not_in; eauto.
  invert H1.
  eapply IHeval1 in H6; eauto.
  eapply IHeval2 in H7; eauto.
  invert H6; invert H7; eauto.

  invert H1; eauto.
  eapply confidential_mono_dumb in H6; eauto; sets.
  invert H1; eauto.
  eapply confidential_mono_dumb in H8; eauto; sets.
  pose H2 as H4.
  eapply IHeval2 in H4; eauto.
  invert H2.
  eapply confidential_mono_dumb with (cv2:= cv) in H7; eauto; sets.
Qed.

Lemma restrict_while_unaffected :
  forall (e : arith) (c : cmd) (v v' : valuation) (pub : set var),
    eval v (while e loop c done) v' ->
    ~ vars e \subseteq pub ->
    Confidential pub (vars e) c ->
    restrict pub v' = restrict pub v.
Proof.
  simplify; induct H; eauto.
  rewrite IHeval2 with (e:=e)(c:=c); eauto.
  eapply restrict_unaffected; eauto.
Qed.


Lemma eval_preserves_public_equiv :
  forall pub c v1 v1',
    eval v1 c v1' ->
  forall v2 v2',
    eval v2 c v2' ->
    Confidential pub {} c ->
    restrict pub v1 = restrict pub v2 ->
    restrict pub v1' = restrict pub v2'.
Proof.
  induct 1; intros.
  - invert H0; invert H.
    eassumption.
  - invert H0; invert H; simplify.
    rewrite restrict_add_not_in; auto.
    rewrite restrict_add_not_in; eauto.

    excluded_middle (pub x).
    --rewrite restrict_add_in; eauto.
      rewrite restrict_add_in; eauto.
      assert (interp e v = interp e v2).
      { eapply interp_eq_when_vars_in; eauto. }

      invert H0; invert H1; eauto.

    --rewrite restrict_add_not_in; eauto.
      rewrite restrict_add_not_in; eauto.


  - invert H1; invert H2; simplify.
    eapply IHeval2 in H9; eauto.

  - invert H1; invert H2; simplify.
    eapply IHeval with (v2 := v2); auto.
    eapply confidential_mono_dumb; eauto; sets.

    assert (~ vars e \subseteq pub) as Hsub.
    {intro. assert (interp e v = interp e v2). simplify.
    eapply interp_eq_when_vars_in; eauto. sets. }

    pose (restrict_unaffected v v' thn pub ({ } \cup vars e)); eauto.
    simplify.
    pose (restrict_unaffected v2 v2' els pub ({ } \cup vars e)); eauto.
    simplify.

    rewrite e1, e0; eauto.
    sets.
    sets.

  - invert H1; invert H2; simplify.
    pose (restrict_unaffected v v' els pub ({ } \cup vars e)); eauto.
    simplify.
    pose (restrict_unaffected v2 v2' thn pub ({ } \cup vars e)); eauto.
    simplify.
    rewrite e1, e0; eauto.

    assert (~ vars e \subseteq pub) as Hsub.
    {intro. assert (interp e v = interp e v2). simplify.
    eapply interp_eq_when_vars_in; eauto. sets. } sets.

    assert (~ vars e \subseteq pub) as Hsub.
    {intro. assert (interp e v = interp e v2). simplify.
    eapply interp_eq_when_vars_in; eauto. sets. } sets.

    eapply IHeval; eauto.
    eapply confidential_mono_dumb; eauto.
    sets.
  - invert H2; invert H3; simplify.
    eapply IHeval2; eauto.
    eapply ConfidentialWhile; eauto.
    invert H11; eauto.
    eapply IHeval1; eauto.
    eapply confidential_mono_dumb; eauto.
    sets.
    eapply confidential_mono_dumb in H6; eauto; sets.

    assert (~ vars e \subseteq pub) as Hsub.
    {intro. assert (interp e v = interp e v2'). simplify.
    eapply interp_eq_when_vars_in; eauto. sets. }

    pose (restrict_while_unaffected e body v' v'' pub H1 ); eauto.
    simplify.
    pose (restrict_unaffected v v' body pub ({ } \cup vars e)); eauto.
    simplify.
    rewrite e0. rewrite e1; eauto.
    sets.
    sets.
    eapply confidential_mono_dumb; eauto.
    sets.
  - invert H0; invert H1; eauto.

    assert (~ vars e \subseteq pub) as Hsub.
    {intro. assert (interp e v = interp e v2). simplify.
    eapply interp_eq_when_vars_in; eauto. sets. }

    pose (restrict_while_unaffected e body v' v2' pub H9); eauto.
    simplify.
    pose (restrict_unaffected v2 v' body pub ({ } \cup vars e)); eauto.
    simplify.
    rewrite e0. rewrite e1; eauto; sets.
    sets.
    eapply confidential_mono_dumb; eauto; sets.
Qed.

(* HINT 1-2 (see Pset8Sig.v) *)
Theorem non_interference :
  forall pub c v1 v1' v2 v2',
    eval v1 c v1' ->
    eval v2 c v2' ->
    Confidential pub {} c ->
    same_public_state pub v1 v2 ->
    same_public_state pub v1' v2'.
Proof.
  simplify.
  unfold same_public_state in *.
  apply eval_preserves_public_equiv with (pub := pub) (c := c) (v1:=v1)(v2:=v2); assumption.
Qed.

(*|
Congratulations, you have proved that our type system is *sound*: it catches all leaky programs!
But it is not *complete*: there are some good programs that it rejects, too.
In other words, it *overapproximates* the set of unsafe programs.

Can you give an example of a safe program (a program that does not leak data) that our system
would reject?
|*)

Definition tricky_example : cmd := when "a" then "x" <- 0 else "x" <- 0 done.

Lemma tricky_rejected : ~ Confidential pub_example {} tricky_example.
Proof.
  unfold tricky_example, pub_example, not; intros H.
  invert H; simplify.
  invert H3; simplify.
  - invert H5; simplify.
    + sets.
    + pose proof (@subseteq_In _ "a" _ _ H4); sets.
  - invert H5; simplify.
    + sets.
    + pose proof (@subseteq_In _ "a" _ _ H6); sets.
Qed.

Lemma tricky_confidential :
  forall v1 v1' v2 v2',
    eval v1 tricky_example v1' ->
    eval v2 tricky_example v2' ->
    same_public_state pub_example v1 v2 ->
    same_public_state pub_example v1' v2'.
Proof.
  intros * He1 He2 Hsame.
  unfold tricky_example, same_public_state in *.
  invert He1; invert He2; try contradiction.
  invert H5; invert H7; simplify.
  excluded_middle ("x" \in pub_example).
  rewrite restrict_add_in; eauto.
  rewrite restrict_add_in; eauto.
  invert Hsame; trivial.
  rewrite restrict_add_not_in; eauto.
  rewrite restrict_add_not_in; eauto.
  invert H5; invert H7; simplify.
  excluded_middle ("x" \in pub_example).
  rewrite restrict_add_in; eauto.
  rewrite restrict_add_in; eauto.
  invert Hsame; trivial.
  rewrite restrict_add_not_in; eauto.
  rewrite restrict_add_not_in; eauto.
  invert H5; invert H7; simplify.
  excluded_middle ("x" \in pub_example).
  rewrite restrict_add_in; eauto.
  rewrite restrict_add_in; eauto.
  invert Hsame; trivial.
  rewrite restrict_add_not_in; eauto.
  rewrite restrict_add_not_in; eauto.
  invert H5; invert H7; simplify.
  excluded_middle ("x" \in pub_example).
  rewrite restrict_add_in; eauto.
  rewrite restrict_add_in; eauto.
  invert Hsame; trivial.
  rewrite restrict_add_not_in; eauto.
  rewrite restrict_add_not_in; eauto.
Qed.
End Impl.

Module ImplCorrect : Pset8Sig.S := Impl.

(* Authors:
   Clément Pit-Claudel
   Dustin Jamner
 *)
