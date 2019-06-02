Require String Vector.
Require Import List FunctionalExtensionality.
Import ListNotations.
Set Universe Polymorphism.
Open Scope type_scope.
Open Scope string_scope.
Set Implicit Arguments.

Section Effect.
  Context (eff : Type)(args rets: eff -> Type).

  Inductive t :=
  | Eff : forall (e : eff), args e -> (rets e -> t) -> t
  | Done.

  Definition step_type (state : Type) := state -> forall (e : eff),
      rets e -> option (state * option { e : eff & args e }).

  Inductive equiv' (state : Type)(step : step_type state) :
    state -> t -> option { e : eff & args e} -> Prop :=
  | Equiv'Eff : forall s e (a : args e) p next op,
      (forall r, step s e r = Some (next r, op r)) ->
      (forall r, equiv' step (next r) (p r) (op r)) ->
      equiv' step s (Eff a p) (Some (existT _ _ a))
  | Equiv'Done : forall s,
      step s = (fun _ _ => None) ->
      equiv' step s Done None.

  Inductive equiv (state : Type)(step : step_type state)(init : state)
    : t -> Prop :=
  | EquivEff : forall e (a : args e) p s,
      step init = (fun _ _ => Some (s, Some (existT _ _ a))) ->
      equiv' step s (Eff a p) (Some (existT _ _ a)) ->
      equiv step init (Eff a p)
  | EquivDone : equiv' step init Done None -> equiv step init Done.

End Effect.

Inductive effect := getNat | putNat | getString | putString.

Definition args_effect (e : effect) :=
  match e with
  | getNat => unit
  | putNat => nat
  | getString => unit
  | putString => String.string
  end.

Definition rets_effect (e : effect) :=
  match e with
  | getNat => nat
  | putNat => unit
  | getString => String.string
  | putString => unit
  end.

Inductive yield_effect := yield : yield_effect.

Definition seqE A B (e : t (fun _:yield_effect => A) (fun _:yield_effect => B)) : (A -> (B -> t (fun _:yield_effect => A) (fun _:yield_effect => B)) -> t args_effect rets_effect) -> t args_effect rets_effect :=
  match e with
  | Done _ _ => fun _ => Done _ _
  | Eff _ a p => fun cont => cont a p
  end.

Notation "n <- 'getNat' ; e" :=
  (Eff getNat tt (fun n => e))
    (at level 100, right associativity).
Notation "'putN' n ; e" :=
  (Eff putNat n (fun _ => e))
    (at level 200).
Notation "s <- 'getString' ; e" :=
  (Eff getString tt (fun s => e))
    (at level 100, right associativity).
Notation "'putString' s ; e" :=
  (Eff putString s (fun _ => e))
    (at level 200).
Notation "n <- 'resume' c $ x ; e" :=
  (seqE (c x) (fun n c => e))
    (at level 100, right associativity).
Notation "v1 <- 'yield' v2 ; e" :=
  (Eff yield v2 (fun v1 => e))
    (at level 100, right associativity).

Definition get_put :=
  n <- getNat;
  putN (S n);
    Done args_effect rets_effect.

Definition ex_coroutine n :=
  m <- yield (S n);
    _ <- yield (n + m)%nat;
    Done (fun _:yield_effect => nat) (fun _ => nat).

Inductive fin_prod : forall n, Vector.t Type n -> Type :=
| FPNil : fin_prod (Vector.nil Type)
| FPCons : forall t n (ts : Vector.t Type n), t -> fin_prod ts -> fin_prod (Vector.cons _ t _ ts).
Require Import Logic.JMeq Logic.Eqdep.

Program Definition caseS'_fp n t (ts : Vector.t Type n)(v : fin_prod (Vector.cons _ t _ ts)) :
  forall (P : fin_prod (Vector.cons _ t _ ts) -> Type)
         (H : forall h hs, P (@FPCons t n ts h hs)), P v:=
  match v with
  | FPCons h hs => _
  | FPNil => _
  end.
Next Obligation.
  inversion Heq_anonymous0.
  apply inj_pair2 in H1.
  inversion H1.
  apply inj_pair2 in H3.
  subst.
  inversion Heq_v.
  apply inj_pair2 in H0.
  subst.
  apply H.
Defined.

Fixpoint nth_fp m (types : Vector.t Type m)(p : fin_prod types) n : Vector.nth types n :=
  match n in Fin.t k return
        forall (types : Vector.t Type k),
          fin_prod types -> Vector.nth types n with
  | @Fin.F1 s =>
    fun (types : Vector.t Type (S s)) =>
      Vector.caseS'
        types
        (fun types => fin_prod types -> Vector.nth types Fin.F1)
        (fun t ts =>
           fun (p : fin_prod (Vector.cons _ t _ ts)) =>
             caseS'_fp p _ (fun (h:t)(_:fin_prod ts) => h))
  | @Fin.FS s n' =>
    fun (types : Vector.t  Type (S s)) =>
      Vector.caseS'
        types
        (fun types => fin_prod types -> Vector.nth types (Fin.FS n'))
        (fun t ts =>
           fun (p : fin_prod (Vector.cons _ t  _ ts)) =>
             caseS'_fp p _ (fun (_:t)(hs:fin_prod ts) =>
                              nth_fp hs n'))
  end types p.

Fixpoint replace_fp n (types : Vector.t Type n)(p : fin_prod types) k (a0 : Vector.nth types k) :=
  match k in Fin.t m return
        forall (types:Vector.t Type m),
          fin_prod types -> Vector.nth types k -> fin_prod types with
  | @Fin.F1 m =>
    fun (types : Vector.t Type (S m)) =>
      Vector.caseS'
        types
        (fun types =>
           fin_prod types -> Vector.nth types Fin.F1 -> fin_prod types)
        (fun t ts =>
           fun (p : fin_prod (Vector.cons _ t _ ts)) a0 =>
             caseS'_fp p _
                       (fun (h:t)(hs:fin_prod ts) => FPCons a0 hs))
  | @Fin.FS m k' =>
    fun (types : Vector.t Type (S m)) =>
      Vector.caseS'
        types
        (fun types =>
           fin_prod types -> Vector.nth types (Fin.FS k') -> fin_prod types)
        (fun t ts =>
           fun (p : fin_prod (Vector.cons _ t _ ts)) a0 =>
             caseS'_fp p _ (fun (h:t)(hs:fin_prod ts) =>
                              FPCons h (replace_fp hs k' a0)))
  end types p a0.

Inductive equiv_parent A B :
  forall n (states : Vector.t Type n),
    (forall k, step_type (fun _:yield_effect => A) (fun _:yield_effect => B) (Vector.nth states k)) ->
    (Vector.t (B -> t (fun _:yield_effect => A)(fun _:yield_effect => B)) n -> t args_effect rets_effect) ->
    (fin_prod states -> t args_effect rets_effect) ->
    Prop :=
| EPDone : forall n states
                  (steps : forall k : Fin.t n, step_type (fun _:yield_effect => A) (fun _:yield_effect => B) (Vector.nth states k)),
    equiv_parent steps (fun _ => Done _ _) (fun _ => Done _ _)
| EPEff : forall n states
                 (steps : forall k : Fin.t n, step_type (fun _:yield_effect => A) (fun _:yield_effect => B)(Vector.nth states k))
                 e a f g,
    (forall r, equiv_parent steps (fun cs => f cs r) (fun ss => g ss r)) ->
    equiv_parent steps (fun cs => Eff e a (f cs)) (fun ss => Eff e a (g ss))
| EPSeq :forall n states x k f f' g
                (steps : forall k : Fin.t n, step_type (fun _:yield_effect => A) (fun _:yield_effect => B) (Vector.nth states k)),
    (forall v cs c, f' cs v c = f v (Vector.replace cs k c)) ->
    (forall v, @equiv_parent _ _ n states steps (f v) (g v)) ->
    equiv_parent steps
        (fun cs => seqE (Vector.nth cs k x) (f' cs))
        (fun ss =>
           match (steps k) (nth_fp ss k) yield x with
           | Some (s', Some (existT _ _ v)) => g v (replace_fp ss k s')
           | _ => Done _ _
           end)
| EPSpawn :
    forall n c f f' x state' states
           (steps : forall k : Fin.t n, step_type (fun _:yield_effect => A) (fun _:yield_effect => B) (Vector.nth states k))
           (step : step_type (fun _:yield_effect => A) (fun _:yield_effect => B) state') init g,
      equiv step init (c x) ->
    (forall v cs c, f' cs v c = f v (Vector.cons _ c _  cs)) ->
      (forall v,
          equiv_parent (fun k : Fin.t (S n) =>
                          Fin.caseS' k (fun k => step_type (fun _:yield_effect => A)(fun _:yield_effect => B) (Vector.nth (Vector.cons _ state' _ states) k)) step (fun k' => steps k'))
                       (f v)
                       (g v)) ->
    equiv_parent steps
        (fun cs => seqE (c x) (f' cs))
        (fun ss =>
           match step init yield x with
           | Some (s', Some (existT _ _ v)) => g v (FPCons init ss)
           | _ => Done _ _
           end).

Definition ex N :=
  let c1 := ex_coroutine in
  let c2 := ex_coroutine in
  n1 <- resume c1 $ 1;
    n2 <- resume c2 $ 2;
  (fix aux N c1 c2 :=
    match N with
    | O => Done args_effect rets_effect
    | S N' =>
      m1 <- resume c1 $ n1;
        putN m1;
        m2 <- resume c2 $ n2;
        putN m2;
        aux N' c1 c2
    end) N c1 c2.

(*
Inductive equiv_parent A B state (steps : list (step_type (fun _ => A) (fun _ => B) state)) :
  (list (B -> t (fun _:yield_effect => A) (fun _:yield_effect => B)) -> t args_effect rets_effect) ->
  (list state -> t args_effect rets_effect) -> Prop :=
| EPDone : equiv_parent steps
                        (fun _ => Done _ _)
                        (fun _ => Done _ _)
| EPEff :
    forall e a p q,
    (forall r, equiv_parent steps (fun cs => p cs r) (fun ss => q ss r)) ->
    equiv_parent steps
            (fun cs => Eff e a (p cs))
            (fun ss => Eff e a (q ss))
| EPSeq : forall d0 d1 d2 x n f f' g,
    (forall v, equiv_parent steps (f v) (g v)) ->
    (forall v cs c, f' cs v c = f v (replace_nth n c cs)) ->
    equiv_parent steps
        (fun cs => seqE (nth n cs d0 x) (f' cs))
        (fun ss =>
           match nth n steps d1 (nth n ss d2) yield x with
           | Some (s', Some (existT _ _ v)) => g v (replace_nth n s' ss)
           | _ => Done args_effect rets_effect
           end).

Lemma equiv_parent_eq' :
  forall A B state (step : step_type (fun _ => A)(fun _ => B) state) f g v c s init,
    equiv_parent step f g ->
    (forall b, step init = (fun _ _ => Some (s, Some (existT _ _ (v b))))) ->
    (forall b, equiv' step s (Eff yield (v b) (c b)) (Some (existT _ _ (v b)))) ->
    f (fun b => Eff yield (v b) (c b)) = g init.
Proof.
  intros.
  induction H.
  auto.
  f_equal.
  extensionality r.
  apply H2.
  simpl.
  rewrite (H0 x).
  clear H2 H0.
  specialize (H1 x).
  revert H1.
  generalize (c x).
  specialize (H (v x)).
  revert H.
  generalize (v x).
  intro.
  generalize (f a)(g a).
  intros t0 t1 H.
  revert s a.
  induction H; intros.
  auto.
  f_equal.
  extensionality r.
  eapply H0; eauto.
  simpl.
  inversion H1.
  subst.
  rewrite H5.
  specialize (H7 x0).
  inversion H7.
  simpl.
  eapply H0.
  subst.
  destruct e.
  rewrite H2.
  rewrite H3.
  auto.
  simpl.
  auto.
Qed.

Lemma equiv_parent_eq :
  forall A B (b:B)state (step : step_type (fun _ => A)(fun _ => B) state) f g v c init,
    equiv_parent step f g ->
    (forall b, equiv step init (Eff yield (v b) (c b))) ->
    f (fun b => Eff yield (v b) (c b)) = g init.
Proof.
  intros.
  assert (equiv step init (v1 <- yield v b; c b v1)) by auto.
  inversion H1.
  subst.
  apply equiv_parent_eq' with step s; intros.
  auto.
  specialize (H0 b0).
  inversion H0; subst.
  rewrite H5 in H4.
  apply equal_f in H4.
  apply equal_f in H4.
  inversion H4.
  subst.
  auto.
  exact b.
  exact yield.
  specialize (H0 b0).
  inversion H0; subst.
  rewrite H5 in H4.
  apply equal_f in H4; [|exact yield].
  apply equal_f in H4; [|exact b].
  inversion H4.
  subst.
  auto.
Qed.

Fixpoint ex N c :=
  match N with
  | O => Done args_effect rets_effect
  | S N' =>
    n <- resume c $ 2;
      putN n;
      ex N' c
  end.

Definition ex'_der state step :
  forall N, {g | @equiv_parent nat nat state step (fun c => ex N c) g}.
Proof.
  induction N; simpl.
  eexists ?[g].
  econstructor.
  eexists ?[g].
  econstructor.
  intros.
  set (tmp := fun c (_:unit) => ex N c).
  match goal with
    |- _ _ _ (?X v) =>
    assert (equiv_parent step
                         (fun c => Eff putNat v (tmp c))
                         (X v));
      [| unfold tmp in *; auto];
        let u := open_constr:(fun v => _) in
        unify X u;
          simpl
  end.
  econstructor.
  intros.
  subst tmp.
  simpl.
  apply (proj2_sig IHN).
Defined.

Definition ex' state step N := proj1_sig (@ex'_der state step N).
*)
(*
Lemma ex_ex' : forall state (step : step_type (fun _:yield_effect => nat) _ state) init N,
    (forall n, equiv step init (ex_coroutine n)) ->
    ex N ex_coroutine = ex' step N init.
Proof.
  intros.
  destruct N.
  unfold ex'.
  unfold ex'_der.
  simpl.
  auto.
  simpl.
  unfold ex', ex'_der, nat_rect.
  simpl.
  specialize (H 2).
  inversion H.
  subst.
  rewrite H2.
  f_equal.
  extensionality u.
  destruct u.
  destruct N; simpl.
  auto.
  inversion H4.
  subst.
  rewrite H5.
  specialize (H7 2).
  inversion H7.
  subst.
  f_equal.
  extensionality u.
  destruct u.
  destruct N; simpl.
  auto.
  rewrite H6.
  specialize (H10 2).
  inversion H10.
  auto.
Qed.

Definition ex' state (step : step_type (fun _:yield_effect => nat)(fun _ => nat) state) : state -> nat ->  t args_effect rets_effect :=
  (fix aux s N :=
     match N with
     | O => Done args_effect rets_effect
     | S N' =>
       match step s yield 2 with
       | Some (s', op) =>
         match op with
         | Some (existT _ _ n) => putN n; aux s' N'
         | None => Done _ _
         end
       | None => Done _ _
       end
     end).

Lemma ex_ex' : forall state (step : step_type (fun _:yield_effect => nat) _ state) init N,
    (forall n, equiv step init (ex_coroutine n)) ->
    ex ex_coroutine N = ex' step init N.
Proof.
  intros.
  unfold ex_coroutine in H.
  simpl in H.
  destruct N; simpl.
  auto.
  specialize (H 2).
  inversion H.
  subst.
  rewrite H2.
  f_equal.
  extensionality u.
  destruct N; simpl.
  auto.
  inversion H4.
  subst.
  rewrite H5.
  specialize (H7 2).
  inversion H7.
  subst.
  f_equal.
  extensionality v.
  destruct N; simpl.
  auto.
  rewrite H6.
  specialize (H10 2).
  inversion H10.
  auto.
Qed.
*)
Definition sum_merge (A B C : Type)(f : A -> C)(g : B -> C)(x : sum A B) :=
  match x with
  | inl a => f a
  | inr b => g b
  end.

Infix "|||" := sum_merge (at level 60).

Ltac curry_lhs :=
  lazymatch goal with
    |- ?x = _ =>
    let rec aux p :=
        lazymatch p with
        | ?f (_,_) =>
          let f' := open_constr:(prod_curry _) in
          unify f f'; unfold prod_curry
        | ?p' _ =>
          aux p'
        end
    in
    aux x
  end.

Ltac pattern_rhs term :=
  match goal with
    |- _ = ?X =>
    let x := fresh in
    set (x := X); pattern term in x; subst x
  end.


Lemma equal_f : forall (A B : Type)(f g : A -> B) x,
    f = g -> f x = g x.
  intros.
  congruence.
Qed.

Ltac unify_fun :=
  simpl;
  repeat curry_lhs;
  let rec unify_fun_aux :=
      lazymatch goal with
        |- _ ?x = _ =>
        lazymatch x with
        | tt =>
          lazymatch goal with
          | |- _ = ?X =>
            let tmp := fresh in
            set (tmp := X); pattern tt at 0 in tmp; subst tmp
          end
         | _ =>
           tryif is_var x then
             pattern_rhs x
           else
             lazymatch goal with
             | H := x |- _ =>
                     pattern_rhs H; cbv delta [H]
             end
        end;
        apply equal_f;
        apply eq_refl
        || unify_fun_aux
      end
  in
  unify_fun_aux.

Ltac dest_sum :=
  lazymatch goal with
  | |- ?g (inl _) _ _ = ?t =>
    let e := open_constr:(_|||_) in
    unify g e
  | |- ?g (inr _) = _ =>
    let e := open_constr:(_|||_) in
    unify g e
  end.

Ltac dest_step :=
  simpl;
  repeat (dest_sum; simpl);
  lazymatch goal with
    |- ?f ?r = _ =>
    pattern_rhs r; apply equal_f
  end;
  lazymatch goal with
    |- ?f _ ?a = ?X =>
    lazymatch a with
    | getNat =>
      let u := open_constr:(fun _ e =>
                            match e as e0 return rets_effect e0 -> _ with
                            | getNat => X
                            | _ => fun _ => None
                            end)
      in
      unify f u
    | putNat =>
      let u := open_constr:(fun _ e =>
                            match e as e0 return rets_effect e0 -> _ with
                            | putNat => X
                            | _ => fun _ => None
                            end)
      in
      unify f u
    | yield =>
      pattern_rhs yield; apply equal_f
    end
  end;
  simpl; apply eq_refl.


Definition get_put_derive :
  {state & {step & {init | @equiv _ _ _ state step init get_put}}}.
Proof.
  unfold get_put.
  eexists.
  eexists ?[step].
  eexists ?[init].
  let e := open_constr:(inl tt) in
  unify ?init e.
  econstructor.
  let e := open_constr:(_ ||| _) in
  unify ?step e.
  simpl.
  unify_fun.
  match goal with
    |- _ _ ?s _ _ =>
    let u := open_constr:(inr (inl tt)) in
    unify s u
  end.
  econstructor; intros.
  simpl.
  dest_step.
  match goal with
    |- _ _ _ _ (?op _) =>
    let u := open_constr:(fun _ => _) in
    unify op u
  end.
  simpl.
  econstructor; intros.
  simpl in *.
  match goal with
    |- _ (?next _) _ r0 = _ =>
    let u := open_constr:(fun r : nat => inr (inr _)) in
    unify next u
  end.
  simpl.
  match goal with
    |- _ ?x _ _ = _ =>
    let u := open_constr:(inl r) in
    unify x u
  end.
  dest_step.
  match goal with
    |- _ _ (?next _) _ (?op _) =>
    let u := open_constr:(fun _ => _) in
    let u' := open_constr:(fun _ => inr (inr (inr _))) in
    unify op u;
      unify next u'
  end.
  simpl.
  econstructor.
  simpl.
  match goal with
    |- ?g ?X = _ =>
    unify X tt
  end.
  pattern_rhs tt.
  apply equal_f.
  reflexivity.
Defined.


Arguments existT {_ _}.

Opaque seqE.
Theorem ex_derive :
  forall N, {g | @equiv_parent nat nat 0 (Vector.nil _)
                               (fun p => Fin.case0 (fun k => step_type (fun _:yield_effect => nat) (fun _:yield_effect => nat) (Vector.nth _ k)) p)
                               (fun _ => ex N)
                               g}.
Proof.
  unfold ex.
  intros.
  eexists.
  econstructor.
  intros.
  unfold ex_coroutine.
  match goal with
    |- _ _ ?init _ =>
    let u := open_constr:(inl tt) in
    unify init u
  end.
  econstructor.
  match goal with
    |- ?step _ = _ =>
    let u := open_constr:(_ ||| _) in
    unify step u
  end.
  simpl.
  pattern_rhs tt.
  apply eq_refl.
  match goal with
    |- _ _ ?s _ _ =>
    let u := open_constr:(inr (inl tt)) in
    unify s u
  end.
  econstructor; intros.
  simpl.
  pattern_rhs r.
  apply equal_f.
  pattern_rhs yield.
  apply equal_f.
  match goal with
    |- ?step _ = _ =>
    let u := open_constr:(_ ||| _) in
    unify step u
  end.
  simpl.
  pattern_rhs tt.
  apply eq_refl.
  match goal with
    |- _ _ (?next r) _ _ =>
    let u := open_constr:(fun r0 => inr (inr (_ r0))) in
    unify next u
  end.
  simpl.
  match goal with
    |- _ _ (inr (inr (?x _))) _ _ =>
    match type of x with
      _ -> ?T =>
      let u := open_constr:(nat + _) in
      unify T u
    end;
    let u := open_constr:(fun r => inl r) in
    unify x u
  end.
  simpl.
  econstructor.
  intros.
  simpl.
  dest_step.
  intros.
  match goal with
    |- _ _ (?next _) _ _ =>
    let u := open_constr:(fun _ => inr (inr (inr tt))) in
    unify next u
  end.
  econstructor.
  simpl.
  pattern_rhs tt.
  apply eq_refl.
  intros.
  match goal with
    |- _ = ?f _ _ =>
    unify f (fun v ccs =>
               let c := @Vector.nth _ 1 ccs Fin.F1 in
               seqE (ex_coroutine 2)
                    (fun (n2 : nat)
                         (c2 : nat ->
                               t (fun _:yield_effect => nat) (fun _:yield_effect => nat)) =>
                       (fix
                          aux (N0 : nat)
                          (c1
                             c0 : nat ->
                                  t (fun _:yield_effect => (args_effect putNat))
                                    (fun _:yield_effect => nat)) {struct N0} :
                          t args_effect rets_effect :=
                          match N0 with
                          | 0 => Done args_effect rets_effect
                          | S N' =>
                            m1 <- resume c1 $ v;
                            (putN m1; m2 <- resume c0 $ n2; (putN m2; aux N' c1 c0))
                          end) N c c2))
  end.
  simpl.
  reflexivity.
  intros.
  simpl.
  econstructor.
  unfold ex_coroutine.
  match goal with
    |- _ _ ?init _ =>
    let u := open_constr:(inl tt) in
    unify init u
  end.
  econstructor.
  match goal with
    |- ?step _ = _ =>
    let u := open_constr:(_ ||| _) in
    unify step u
  end.
  simpl.
  pattern_rhs tt.
  apply eq_refl.
  match goal with
    |- _ _ ?s _ _ =>
    let u := open_constr:(inr (inl tt)) in
    unify s u
  end.
  econstructor; intros.
  simpl.
  pattern_rhs r.
  apply equal_f.
  pattern_rhs yield.
  apply equal_f.
  match goal with
    |- ?step _ = _ =>
    let u := open_constr:(_ ||| _) in
    unify step u
  end.
  simpl.
  pattern_rhs tt.
  apply eq_refl.
  match goal with
    |- _ _ (?next r) _ _ =>
    let u := open_constr:(fun r0 => inr (inr (_ r0))) in
    unify next u
  end.
  simpl.
  match goal with
    |- _ _ (inr (inr (?x _))) _ _ =>
    match type of x with
      _ -> ?T =>
      let u := open_constr:(nat + _) in
      unify T u
    end;
    let u := open_constr:(fun r => inl r) in
    unify x u
  end.
  simpl.
  econstructor.
  intros.
  simpl.
  dest_step.
  intros.
  match goal with
    |- _ _ (?next _) _ _ =>
    let u := open_constr:(fun _ => inr (inr (inr tt))) in
    unify next u
  end.
  econstructor.
  simpl.
  pattern_rhs tt.
  apply eq_refl.
  intros.
  match goal with
    |-  _ = ?f _ _ =>
    unify f (fun v0 ccs =>
               let c := @Vector.nth _ 2 ccs Fin.F1 in
               (fix
                  aux (N0 : nat)
                  (c1
                     c0 : nat ->
                          t (fun _:yield_effect => nat) (fun _:yield_effect => nat))
                  {struct N0} : t args_effect rets_effect :=
                  match N0 with
                  | 0 => Done args_effect rets_effect
                  | S N' =>
                    m1 <- resume c1 $ v;
                    (putN m1; m2 <- resume c0 $ v0; (putN m2; aux N' c1 c0))
                  end) N (Vector.nth ccs (Fin.FS Fin.F1)) c)
  end.
  simpl.
  apply eq_refl.
  intros.
  simpl.
  match goal with
    |- _ (?g _) =>
    pattern g;
      match goal with
        |- ?G _ =>
        unshelve (evar (e : {h | G h});
        eassert (E := e : {h | G h}))
      end
  end.
  induction N; eexists; simpl.
  econstructor.
  set (F := fun ccs : Vector.t _ 2 =>  (fun (m1 : nat)
          (c1 : nat ->
                t (fun _:yield_effect => nat) (fun _:yield_effect => nat))
        =>
        putN m1;
        seqE (Vector.nth ccs Fin.F1 v0)
          (fun (m2 : nat)
             (c0 : nat ->
                   t (fun _:yield_effect => nat)
                     (fun _:yield_effect => nat)) =>
           putN m2;
           (fix
            aux (N0 : nat)
                (c2
                 c3 : nat ->
                      t (fun _:yield_effect => nat)
                        (fun _:yield_effect => nat)) {struct N0} :
              t args_effect rets_effect :=
              match N0 with
              | 0 => Done args_effect rets_effect
              | S N' =>
                  m0 <- resume c2 $ v;
                  (putN m0; m3 <- resume c3 $ v0; (putN m3; aux N' c2 c3))
              end) N c1 c0))).
  match goal with
    |- _ ?F' (?g _) =>
    replace F' with (fun ccs : Vector.t _ 2 => seqE (Vector.nth ccs (Fin.FS Fin.F1) v) (F ccs)) by (unfold F; auto);
      let u := open_constr:(fun v0 => _) in
      unify g u
  end.
  simpl.
  eapply EPSeq.
  intros.
  subst F.
  cbv beta.
  match goal with
    |- _ = ?f _ _ =>
    unify f (fun v1 cs =>
               let c := @Vector.nth _ 2 cs (Fin.FS Fin.F1) in
               (putN v1;
                seqE (Vector.nth cs Fin.F1 v0)
                     (fun (m2 : nat)
                          (c0 : nat ->
                                t (fun _ : yield_effect => nat) (fun _ : yield_effect => nat)) =>
                        putN m2;
                        (fix
                           aux (N0 : nat)
                           (c2
                              c3 : nat ->
                                   t (fun _ : yield_effect => nat) (fun _ : yield_effect => nat))
                           {struct N0} : t args_effect rets_effect :=
                           match N0 with
                           | 0 => Done args_effect rets_effect
                           | S N' =>
                             m0 <- resume c2 $ v;
                             (putN m0; m3 <- resume c3 $ v0; (putN m3; aux N' c2 c3))
                           end) N c c0)))
  end.
  cbv beta.
  f_equal.
  extensionality d.
  f_equal.
  apply equal_f.
  eapply (@Vector.caseS' _ 1 cs).
  auto.
  extensionality m.
  extensionality c0.
  f_equal.
  extensionality dummy.
  f_equal.
  eapply (@Vector.caseS' _ 1 cs).
  intros.
  eapply (@Vector.caseS' _ 0 t0).
  auto.

  intros.
  simpl.
  subst F.
  set (F := fun cs : Vector.t _ 2 => (fun (m2 : nat)
          (c0 : nat ->
                t (fun _ : yield_effect => nat) (fun _ : yield_effect => nat))
        =>
        putN m2;
        (fix
         aux (N0 : nat)
             (c2
              c3 : nat ->
                   t (fun _ : yield_effect => nat)
                     (fun _ : yield_effect => nat)) {struct N0} :
           t args_effect rets_effect :=
           match N0 with
           | 0 => Done args_effect rets_effect
           | S N' =>
               m0 <- resume c2 $ v;
               (putN m0; m3 <- resume c3 $ v0; (putN m3; aux N' c2 c3))
           end) N (Vector.nth cs (Fin.FS Fin.F1)) c0)).
  match goal with
    |- _ ?F' (?g _) =>
    replace F' with (fun ccs : Vector.t _ 2 => putN v1; seqE (Vector.nth ccs Fin.F1 v0) (F ccs)) by (unfold F; auto);
      let u := open_constr:(fun v0 => _) in
      unify g u
  end.
  simpl.
  econstructor.
  intros.
  match goal with
    |- _ (fun ss => ?x ss r) =>
    let u := open_constr:(fun ss r => _) in
    unify x u
  end.
  simpl.
  econstructor.
  intros.
  subst F.
  cbv beta.
  match goal with
    |- _ = ?f _ _ =>
    unify f (fun v2 (cs:Vector.t _ 2) =>
               let c := Vector.nth cs Fin.F1 in
               (putN v2;
                (fix
                   aux (N0 : nat)
                   (c2
                      c3 : nat ->
                           t (fun _ : yield_effect => nat) (fun _ : yield_effect => nat))
                   {struct N0} : t args_effect rets_effect :=
                   match N0 with
                   | 0 => Done args_effect rets_effect
                   | S N' =>
                     m0 <- resume c2 $ v;
                     (putN m0; m3 <- resume c3 $ v0; (putN m3; aux N' c2 c3))
                   end) N (Vector.nth cs (Fin.FS Fin.F1)) c))
  end.
  cbv beta.
  f_equal.
  extensionality dummy.
  f_equal.
  eapply (@Vector.caseS' _ 1 cs).
  auto.
  eapply (@Vector.caseS' _ 1 cs).
  auto.

  intros.
  subst F.
  cbv beta.
  set (F := fun cs :Vector.t _ 2 =>
      (fix
       aux (N0 : nat)
           (c2
            c3 : nat ->
                 t (fun _ : yield_effect => nat) (fun _ : yield_effect => nat))
           {struct N0} : t args_effect rets_effect :=
         match N0 with
         | 0 => Done args_effect rets_effect
         | S N' =>
             m0 <- resume c2 $ v;
             (putN m0; m3 <- resume c3 $ v0; (putN m3; aux N' c2 c3))
         end) N (Vector.nth cs (Fin.FS Fin.F1)) (Vector.nth cs Fin.F1)).
  match goal with
    |- _ ?F' (?g _) =>
    replace F' with (fun cs : Vector.t _ 2 => putN v2; F cs) by (unfold F; auto);
      let u := open_constr:(fun v0 => _) in
      unify g u
  end.
  simpl.
  econstructor.
  intros.
  subst F.
  simpl.
  match goal with
    |- _ (fun ss => ?X ss r0) =>
    let u := open_constr:(fun ss r0 => _) in
    unify X u
  end.
  simpl.
  apply (proj2_sig IHN).
  simpl.
  pose (proj2_sig e).
  unfold e in e0.
  simpl in e0.
  apply e0.
Defined.
Transparent seqE.

Eval cbv [ex_derive ex proj1_sig nat_rect] in (fun N => proj1_sig (ex_derive N)).
