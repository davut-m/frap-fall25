(*|
===========================================================
 6.512 Formal Reasoning About Programs, Fall 2025 - Pset 10
===========================================================
|*)

Require Export Frap.Frap.

From Stdlib Require Import ZArith Lia.
From Stdlib Require Import Structures.OrdersEx.
From Stdlib Require Import Sorting.Mergesort.

Open Scope Z_scope.

Module ZLeBool <: Orders.TotalLeBool.
  Definition t := Z.
  Definition leb := Z.leb.
  Theorem leb_total (x y : t) :
    leb x y = true \/ leb y x = true.
  Proof.
    unfold leb.
    destruct (Z_le_gt_dec x y) as [Hle | Hgt].
    - left.  now rewrite Z.leb_le.
    - right. rewrite Z.leb_le; lia.
  Qed.
End ZLeBool.

Module ZSort := Mergesort.Sort(ZLeBool).

Module Type S.
  Inductive binop := Add | Mul | Sub.

  Inductive rhs :=
  | Const (n : Z)
  | Binop (b : binop) (x y : var).

  Record instr := Instr {
                      Lhs : var;
                      Rhs : rhs
                    }.

  Definition prog := list instr.

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

  Definition node := Z.

  Inductive node_kind :=
  | SConst (n : Z)
  | SVar (x : var)
  | SAdd (n : Z) (args : list node)
  | SMul (n : Z) (args : list node)
  | SSub (x : node) (y : node).

  Definition nodes_in := fmap node_kind node.
  Definition nodes_out := fmap node node_kind.
  Definition varmap := fmap var node.

  Record sstate := SState {
                       NodesIn : nodes_in;
                       NodesOut : nodes_out;
                       NextNode : node;
                       Vars : varmap
                     }.

  Definition node_kind_in (st : sstate) (nk : node_kind) : sstate * node :=
    match st.(NodesIn) $? nk with
    | None => ({| NodesIn := st.(NodesIn) $+ (nk, st.(NextNode));
                 NodesOut := st.(NodesOut) $+ (st.(NextNode), nk);
                 NextNode := st.(NextNode) + 1;
                 Vars := st.(Vars) |},
                st.(NextNode))
    | Some nd => (st, nd)
    end.

  Definition dummy := SConst 0.

  Infix "==z" := Z.eq_dec (no associativity, at level 50).

  Definition symAddOf (st : sstate) (nd : node) : Z * list node :=
    match st.(NodesOut) $? nd with
    | Some (SAdd n args) => (n, args)
    | Some (SConst n) => (n, [])
    | _ => (0, [nd])
    end.

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

  Definition kindOfRhs (st : sstate) (r : rhs) : node_kind :=
    match r with
    | Const n => SConst n
    | Binop Sub x y =>
        match st.(Vars) $? x, st.(Vars) $? y with
        | Some nx, Some ny =>
            match st.(NodesOut) $? nx, st.(NodesOut) $? ny with
            | Some nkx, Some (SConst n) =>
                if n ==z 0 then
                  nkx
                else
                  SSub nx ny
            | _, _ => SSub nx ny
            end
        | _, _ => dummy
        end
    | Binop Add x y =>
        match st.(Vars) $? x, st.(Vars) $? y with
        | Some nx, Some ny =>
            let (n1, args1) := symAddOf st nx in
            let (n2, args2) := symAddOf st ny in
            let args := ZSort.merge args1 args2 in
            if isNil args then
              SConst (n1 + n2)
            else
              SAdd (n1 + n2) args
        | _, _ => dummy
        end
    | Binop Mul x y =>
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

  Definition symInstr (st : sstate) (i : instr) : sstate :=
    let (st, n) := node_kind_in st (kindOfRhs st i.(Rhs)) in
    {| NodesIn := st.(NodesIn);
      NodesOut := st.(NodesOut);
      NextNode := st.(NextNode);
      Vars := st.(Vars) $+ (i.(Lhs), n) |}.

  Definition symProg : prog -> sstate -> sstate :=
    fold_left symInstr.

  Definition inputs := {"a", "b", "c"}.

  Definition initial : sstate :=
    {| NodesIn := $0 $+ (SVar "a", 0) $+ (SVar "b", 1) $+ (SVar "c", 2);
      NodesOut := $0 $+ (0, SVar "a") $+ (1, SVar "b") $+ (2, SVar "c");
      NextNode := 3;
      Vars := $0 $+ ("a", 0) $+ ("b", 1) $+ ("c", 2) |}.

  Definition redoVars (st : sstate) : sstate :=
    {| NodesIn := st.(NodesIn);
      NodesOut := st.(NodesOut);
      NextNode := st.(NextNode);
      Vars := $0 $+ ("a", 0) $+ ("b", 1) $+ ("c", 2) |}.

  Definition equivalent (pr1 pr2 : prog) : bool :=
    let st := initial in
    let st := symProg pr1 st in
    let out1 := st.(Vars) $? "out" in
    let st := redoVars st in
    let st := symProg pr2 st in
    let out2 := st.(Vars) $? "out" in
    match out1, out2 with
    | Some out1, Some out2 => Z.eqb out1 out2
    | _, _ => false
    end.

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

  (*[100%]*)Axiom equivalent_correct : forall pr1 pr2,
      equivalent pr1 pr2 = true
      -> (progReads pr1 \cup progReads pr2) \subseteq inputs
      -> forall v, evalProg pr1 v $! "out" = evalProg pr2 v $! "out".
End S.

(*|
TIPS
====

- To prove a property of [ZSort.merge ls1 ls2] by induction, begin the proof with
  [induct ls1; induct ls2].  We rarely consider nested inductions within single
  lemmas, but it turns out to be the right way to deal with the clever recursive
  structure of this function.
|*)

(*|
HINTS: A few hints to help you if you get stuck on certain 
       problems in Pset 10.
       Beware! Don't read further if you don't want spoilers!
=============================================================
|*)































(*| We're glad to give full credit for any proof of the designated main theorem,
  but it's a relatively involved proof, so we also give the great majority of a
  solution below, with notes on how we will assign partial credit for the
  unproved lemmas that we have left.

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
  Admitted.

  (* Symmetrical one for multiplication: *)
  (*[15%]*)Lemma symMulOf_correct : forall st v0 v nvs n z l,
      compat st v0 v nvs
      -> st.(NodesOut) $? n <> None
      -> symMulOf st n = (z, l)
      -> nvs $? n = Some (product (map (fun nd => nvs $! nd) l) z).
  Proof.
  Admitted.

  (* We will need to know that merging sums and products has the expected
   * effects, and one way to go about it is proving properties generically for
   * associative-commutative operators. *)
  Section associative_commutative.
    Variable f : Z -> Z -> Z.
    Hypothesis commutative : forall x y, f x y = f y x.
    Hypothesis associative : forall x y z, f (f x y) z = f x (f y z).

    Variable g : Z -> Z.

    (*[35%]*)Lemma merge_combine : forall l1 n1 l2 n2,
        fold_left f (map g (ZSort.merge l1 l2)) (f n1 n2)
        = f (fold_left f (map g l1) n1) (fold_left f (map g l2) n2).
    Proof.
    Admitted.
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
  Admitted.

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
|*)
