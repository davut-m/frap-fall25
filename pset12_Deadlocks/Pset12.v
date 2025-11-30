(** * 6.512 Formal Reasoning About Programs, Fall 2025 - Pset 12 *)

Require Import Frap Pset12.Pset12Sig.

(* Programmers who start programming with threads and locks soon realize that it
 * is tricky to avoid *deadlocks*, where thread #1 is waiting to take a lock
 * held by thread #2, and thread #2 is waiting to take a lock held by thread #3,
 * and... thread #N is waiting to take a lock held by thread #1.  That's a wait
 * cycle, and none of the threads will ever make progress.
 *
 * The most common wisdom about avoiding deadlocks is to impose a *total order*
 * on the locks.  A thread is only allowed to acquire a lock that is *less than*
 * all locks it currently holds.  In this pset, we formalize a simple static
 * analysis checking that the total-order rule is obeyed, and we prove that any
 * program accepted by the analysis avoids deadlock. *)

(* Please start by reading the definitions in Pset12Sig.v! *)

(* Before diving into the proof hacking, it might be helpful to write a short
   sample program (in Rocq) where thread 1 acquires lock 1 and then lock 2,
   while thread 2 tries to acquire lock 2 and then lock 1, and explain (in
   English) how a deadlock can happen: *)

Example bad: prog. Admitted.

(* FILL IN explanation here *)


(* And now, explain why the total-order rule would reject your example by copy-pasting
   the one rule which rejects it from Pset12Sig.v and briefly describing how it would
   reject it: *)

(* FILL IN explanation here *)

(* The two questions above are not graded, but we hope they help you understand
   the material better! *)

(* Since we use the [a_useful_invariant] theorem, proving [deadlock_freedom]
   reduces to proving this lemma — the only one in this Pset!  See hints at the bottom
   of the signature file if you get stuck, and of course come to office hours if you
   have any questions or need help. *)



Module Impl.
(* HINT 1-5 (see Pset12Sig.v) *)

Lemma who_has_the_lock'' : forall h a l l1 c l2,
      goodCitizen l1 c l2
      -> a \in l1
      -> l1 \subseteq l
      -> finished c
         \/ (exists h' l' c', step0 (h, l, c) (h', l', c'))
         \/ (exists a', a' < a /\ a' \in l).
Proof.
   simplify.
   induct H; eauto.
   - assert (IH1 := IHgoodCitizen H2 H3).
     destruct IH1 as [Hfin | [Hstep | Hsmaller]].
     + invert Hfin.
       right; left. eauto.
     + right; left.
       cases Hstep.
       cases H4; cases H4.
       exists x, x0, (Bind x1 c2).
       econstructor; eauto.
     + right; right; eauto.
   - right; eauto.
   - right; left; eauto.
   - assert (a0 \in l \/ ~a0 \in l) by (sets).
     destruct H2.
     + right; right.
      exists a0. split.
      apply H in H0. linear_arithmetic.
      assumption.
     + right; left.
       exists h, (l \cup {a0}), (Return 0).
       constructor. assumption.
   - right; left.
     pose (StepUnlock h l a); eauto.
     assert (a0 \in l); sets; eauto.
Qed.



Lemma who_has_the_lock' : forall h a l l1 c,
      goodCitizen l1 c {}
      -> a \in l1
      -> l1 \subseteq l
      -> (exists h' l' c', step0 (h, l, c) (h', l', c'))
        \/ (exists a', a' < a /\ a' \in l).
Proof.
   simplify.
   pose proof (who_has_the_lock'' h a l l1 c {} H H0 H1) as H2.
   destruct H2.
   - invert H2.
     invert H.
     sets.
   - eauto.
Qed.


Lemma who_has_the_lock : forall l h a p,
      Forall (fun l_c => goodCitizen (fst l_c) (snd l_c) {}) p
      -> a \in locksOf p
      -> locksOf p \subseteq l
      -> (exists h_l_p', step (h, l, progOf p) h_l_p')
        \/ (exists a', a' < a /\ a' \in l).
Proof.
   simplify.
   induct p.
   - sets.
   - cases a0; simplify.
     invert H.
     simplify.
     assert (a \in s \/ a \in locksOf p) by sets.
     cases H.
     -- assert (s \subseteq l) by sets.
        pose proof (who_has_the_lock' h a l s c H4 H H2).
        cases H3; eauto.
        left.
        cases H3; cases H3; cases H3.
        exists (x, x0, (x1 :: progOf p)).
        simplify.
        apply StepThread1.
        eauto.
     -- assert (locksOf p \subseteq l) by sets.
        pose proof (IHp H5 H H2) as IH.
        cases IH; eauto.
        left.
        cases IH.
        cases x.
        cases p0.
        eapply step_cat; eauto.
Qed.

Lemma if_no_locks_held_then_progress' : forall h c l,
   goodCitizen {} c l ->
   finished c \/ exists h' l' c', step0 (h, {}, c) (h', l', c').
Proof.
   simplify.
   induct H; simplify; eauto.
   - destruct IHgoodCitizen; eauto.
     invert H2; eauto.
     right.

     invert H2.
     cases H3. cases H2.
     eexists; eexists; eexists.
     eapply StepBindRecur.
     eauto.
   - right.
     eexists; eexists; eexists.
     eapply StepLock.
     eauto.
   - left.
     invert H.
Qed.


Theorem if_no_locks_held_then_progress : forall h p,
      Forall (fun l_c => goodCitizen (fst l_c) (snd l_c) {}) p
      -> locksOf p = {}
      -> Forall (fun l_c => finished (snd l_c)) p
        \/ exists h_l_p', step (h, locksOf p, progOf p) h_l_p'.
Proof.
   simplify.
   induct H; simplify; eauto.

   cases x.
   assert (locksOf l = {}) by (sets).
   eapply IHForall in H2; eauto.
   cases c; eauto.

   - cases H2.
     left.
     replace ((s, Return r) :: l) with ([(s, Return r)] ++ l) by equality.
     eapply Forall_app_bwd; eauto.
     econstructor; eauto.
     econstructor; eauto.
     cases H2.
     right.
     eapply step_cat; eauto.
     rewrite H1; simplify.
     assert (locksOf l = { }) by sets.
     invert H3; eauto.

   -  invert H.
      assert (s = { }) by (sets).
      subst.
      eapply if_no_locks_held_then_progress' in H6.
      propositional; eauto.
      invert H2.
      right.
      eexists.
      eapply StepThread1; eapply StepBindProceed.

      right.
      cases H2; cases H2; cases H2.
      eexists.
      eapply StepThread1; eapply StepBindRecur.
      rewrite H1; eauto.

      invert H2.
      right.
      eexists.
      eapply StepThread1; eapply StepBindProceed.

      invert H2.
      right.
      cases H3. cases H2.
      eexists.
      eapply StepThread1; eapply StepBindRecur.
      rewrite H1; eauto.
   - cases H2.
     right.
     rewrite H1; simplify.
     eexists; eapply StepThread1.
     econstructor; eauto.

     cases H2.
     right.
     eapply step_cat; eauto.
     assert (s = { }) by sets.
     assert (s \cup locksOf l = locksOf l ) by sets.
     rewrite H4; eauto.
   -  cases H2.
      right.
      rewrite H1; simplify.
      eexists; eapply StepThread1.
      econstructor; eauto.
      invert H; sets.

     cases H2.
     right.
     eapply step_cat; eauto.
     assert (s = { }) by sets.
     assert (s \cup locksOf l = locksOf l ) by sets.
     rewrite H4; eauto.
Qed.

Theorem if_lock_held_then_progress : forall bound a h p,
    Forall (fun l_c => goodCitizen (fst l_c) (snd l_c) {}) p
    -> a \in locksOf p
    -> a < bound
    -> Forall (fun l_c => finished (snd l_c)) p
       \/ exists h_l_p', step (h, locksOf p, progOf p) h_l_p'.
Proof.
   simplify.
   induct bound.
   - assert (a = 0). linear_arithmetic.
     linear_arithmetic.
   - simplify.
     eapply who_has_the_lock in H0; eauto.
     propositional; eauto.
     cases H2.
     propositional; eauto.
Qed.



Lemma deadlock_freedom' :
  forall (h : heap) (p : prog'),
  Forall (fun l_c : locks * cmd => goodCitizen (fst l_c) (snd l_c) { }) p ->
  Forall finished (progOf p) \/ (exists h_l_p' : heap * locks * prog,
                                    step (h, locksOf p, progOf p) h_l_p').
Proof.
   simplify.
   excluded_middle (exists a, a \in locksOf p).
   -  first_order.
      assert (x < x+1) by linear_arithmetic.
      pose (if_lock_held_then_progress (x+1) x h p H H0 H1); simplify.
      invert o; eauto.
  -   assert (locksOf p = {}) as Hempty.
      sets; eauto.
      pose (if_no_locks_held_then_progress h p H Hempty); eauto.
      invert o; eauto.
Qed.

(* Here's how we can use [a_useful_invariant] to go from [deadlock_freedom'] to
   [deadlock_freedom]: *)
Theorem deadlock_freedom :
  forall h p,
    Forall (fun c => goodCitizen {} c {}) p ->
    invariantFor (trsys_of h {} p) (fun h_l_p =>
                                      let '(_, _, p') := h_l_p in
                                      Forall finished p'
                                      \/ exists h_l_p', step h_l_p h_l_p').
Proof.
  (* To begin with, we strengthen the invariant to the one proved in Pset12Sig. *)
  simplify.
  eapply invariant_weaken.
  eauto using a_useful_invariant.

  (* What's left is to prove that this invariant implies deadlock-freedom. *)
  first_order.
  destruct s as [[h' ls] p'].
  invert H0.

  (* We don't actually need to use the [disjointLocks] property.  It was only
   * important in strengthening the induction to prove that other invariant. *)
  clear H6.

  (* At this point, we apply the lemma that we expect you to prove! *)
  apply deadlock_freedom'. assumption.
Qed.
End Impl.

Module ImplCorrect : Pset12Sig.S := Impl.

(* Authors:
   Adam Chlipala,
   Peng Wang,
   Samuel Gruetter *)
