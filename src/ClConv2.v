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
    state -> t -> option { e : eff & args e } -> Prop :=
  | Equiv'Eff : forall s e (a : args e) p next op,
      (forall r, step s e r = Some (next s r, op s r)) ->
      (forall r, equiv' step (next s r) (p r) (op s r)) ->
      equiv' step s (Eff a p) (Some (existT _ _ a))
  | Equiv'Done : forall s,
      step s = (fun _ _ => None) ->
      equiv' step s Done None.

  Definition equiv state (step : step_type state) init p :=
    exists op s, step init = (fun _ _ => Some (s, op)) /\ equiv' step s p op.

  (*Inductive equiv (state : Type)(step : step_type state)(init : state)
    : t -> Prop :=
  | EquivEff : forall e (a : args e) p s,
      step init = (fun _ _ => Some (s, Some (existT _ _ a))) ->
      equiv' step s (Eff a p) (Some (existT _ _ a)) ->
      equiv step init (Eff a p)
  | EquivDone : equiv' step init Done None -> equiv step init Done.
*)
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

Notation "n <- 'getN' ; e" :=
  (Eff getNat (tt : args_effect getNat) (fun n : rets_effect getNat => e))
    (at level 100, right associativity).
Notation "'putN' n ; e" :=
  (Eff putNat (n : args_effect putNat) (fun _ => e))
    (at level 200).
Notation "s <- 'getStr' ; e" :=
  (Eff getString tt (fun s => e))
    (at level 100, right associativity).
Notation "'putStr' s ; e" :=
  (Eff putString s (fun _ => e))
    (at level 200).
Notation "n <- 'resume' c $ x ; e" :=
  (seqE (c x) (fun n c => e))
    (at level 100, right associativity).
Notation "v1 <- 'yield' v2 ; e" :=
  (Eff yield v2 (fun v1 => e))
    (at level 100, right associativity).

Definition get_put : t args_effect rets_effect :=
  n <- getN;
  putN (S n);
    Done _ _.

Definition ex_coroutine n : t (fun _:yield_effect => nat) (fun _:yield_effect => nat):=
  m <- yield (S n);
    _ <- yield (n + m)%nat;
    Done _ _.

Inductive fin_prod : forall n, Vector.t Type n -> Type :=
| FPNil : fin_prod (Vector.nil Type)
| FPCons : forall t n (ts : Vector.t Type n), t -> fin_prod ts -> fin_prod (Vector.cons _ t _ ts).

Definition caseS'_fp n t (ts : Vector.t Type n)(v : fin_prod (Vector.cons _ t _ ts)) :
  forall (P : fin_prod (Vector.cons _ t _ ts) -> Type)
         (H : forall h hs, P (@FPCons t n ts h hs)), P v :=
  (fun v0 : fin_prod (Vector.cons Type t n ts) =>
 match
   v0 as v1 in (@fin_prod n0 iV)
   return
     (match iV as iV0 in (Vector.t _ n1) return (fin_prod iV0 -> Type) with
      | Vector.nil _ =>
          fun _ : fin_prod (Vector.nil Type) => forall x : Type, x -> x
      | Vector.cons _ t0 n1 ts0 =>
          fun v2 : fin_prod (Vector.cons Type t0 n1 ts0) =>
          forall P : fin_prod (Vector.cons Type t0 n1 ts0) -> Type,
          (forall (h : t0) (hs : fin_prod ts0), P (FPCons h hs)) -> P v2
      end v1)
 with
 | FPNil => fun (A : Type) (x : A) => x
 | @FPCons t0 n0 ts0 h hs =>
     fun (P : fin_prod (Vector.cons Type t0 n0 ts0) -> Type)
       (X : forall (h0 : t0) (hs0 : fin_prod ts0), P (FPCons h0 hs0)) => 
     X h hs
 end) v.

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
           | Some (s', Some (existT _ _ v)) => g v (FPCons s' ss)
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
  | |- ?g (inr _) _ _ = _ =>
    let e := open_constr:(_|||_) in
    unify g e
  | |- ?g (inl _) = ?t =>
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
      let u := open_constr:(fun x e =>
                            match e as e0 return rets_effect e0 -> _ with
                            | getNat => X
                            | _ => fun _ => None
                            end)
      in
      unify f u
    | putNat =>
      let u := open_constr:(fun x e =>
                            match e as e0 return rets_effect e0 -> _ with
                            | putNat => X
                            | _ => fun _ => None
                            end)
      in
      unify f u
    | yield =>
      pattern_rhs yield; apply equal_f
    end
  | _ => idtac
  end;
  simpl; apply eq_refl.


Definition get_put_derive :
  {state & {step & {init | @equiv _ _ _ state step init get_put}}}.
Proof.
  unfold get_put, equiv.
  eexists.
  eexists ?[step].
  eexists ?[init].
  eexists.
  eexists.
  let e := open_constr:(inl tt) in
  unify ?init e.
  split.
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
    |- _ _ _ _ (?op _ _) =>
    let u := open_constr:(fun _ _ => _) in
    unify op u
  end.
  simpl.
  econstructor; intros.
  simpl in *.
  match goal with
    |- _ (?next _ _) _ r0 = _ =>
    let u := open_constr:(fun _ (r : nat) => inr (inr _)) in
    unify next u
  end.
  simpl.
  match goal with
    |- _ ?x _ _ = _ =>
    let u := open_constr:(inl r) in
    unify x u
  end.
  dest_sum.
  simpl.
  pattern_rhs r0.
  apply equal_f.
  match goal with
    |- ?f _ _ = ?X =>
    match X with
      (fun u => Some (?next _ _ , ?op _ _ )) =>
      let ty := type of next in
      let u' := open_constr:(_ -> _ -> _+(_+(_+(_+_)))) in
      unify ty u';
      let u := open_constr:(fun _ _ => inr (inr (inr (inl tt)))) in
      unify next u;
        let u := open_constr:(fun _ r => _) in
        unify op u
    end
  end.
  simpl.
  match goal with
    |- ?f _ _ = ?X =>
    let u := open_constr:(fun x e =>
                            match e as e0 return rets_effect e0 -> _ with
                            | putNat => _
                            | _ => fun _ => None
                            end)
    in
    unify f u
  end.
  simpl.
  2:simpl;econstructor.
  apply eq_refl.
  simpl.
  match goal with
    |- ?g _ = ?X =>
    let u := open_constr:(fun _ => X) in
    unify g u
  end.
  simpl.
  reflexivity.
  Grab Existential Variables.
  exact unit.
Defined.


Opaque seqE.
Theorem ex_derive_parent :
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
  do 2 eexists.
  split.
  dest_step.
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
  dest_step.
  simpl.
  match goal with
    |- _ _ (?next _ r) _ (?op _ _) =>
    let u := open_constr:(fun _ r0 => inr (inr (_ r0))) in
    unify next u;
      let u := open_constr:(fun _ r => _) in
      unify op u
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
    |- _ _ (?next _ _) _ (?op _ _) =>
    let u := open_constr:(fun _ _ => inr (inr (inr tt))) in
    unify next u;
      let u := open_constr:(fun _ _ => _) in
      unify op u
  end.
  econstructor.
  simpl.
  pattern_rhs tt.
  apply eq_refl.
  intros.
  (*
  match goal with
    |- ?lhs = ?f _ ?ccs0 =>
    set (ccs := ccs0)
  end.
  replace c with (@Vector.nth _ 1 ccs Fin.F1) by (subst ccs; auto).
  lazymatch goal with
    |- _ = ?f _ _ =>
    let u := open_constr:(fun v ccs => _) in
    unify f u
  end.
  apply eq_refl.
*)
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
  do 2 eexists.
  split.
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
    |- _ _ (?next _ r) _ (?op _ _) =>
    let u := open_constr:(fun _ r0 => inr (inr (_ r0))) in
    unify next u;
      let u := open_constr:(fun _ r => _) in
      unify op u
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
    |- _ _ (?next _ _) _ (?op _ _) =>
    let u := open_constr:(fun _ _ => inr (inr (inr tt))) in
    unify next u;
      let u := open_constr:(fun _ _ => _) in
      unify op u
  end.
  econstructor.
  simpl.
  pattern_rhs tt.
  apply eq_refl.
  intros.
  (*
  lazymatch goal with
    |- _ = ?f _ ?ccs0 =>
    set (ccs := ccs0);
      replace c with (@Vector.nth _ 2 ccs Fin.F1) by (subst ccs; auto);
      replace cs with (Vector.tl ccs) by (subst ccs; auto);
      let u := open_constr:(fun v0 ccs => _) in
      unify f u
  end.
  apply eq_refl.
*)
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

Definition dummy := fun (A:Type)(_:A) => True.

Theorem ex_correct : forall N,
    ex N = proj1_sig (ex_derive_parent N) FPNil.
Proof.
  unfold ex.
  simpl.
  destruct N; intros.
  simpl.
  auto.
  simpl.
  f_equal.
  extensionality u.
  f_equal.
  extensionality u0.
  f_equal.
  destruct N; simpl; auto.
Qed.

Theorem ex_derive :
  {state & {step & forall N, {init | @equiv _ _ _ state step init (ex N)}}}.
Proof.
  set (ty_v := fin_prod
        (Vector.cons Set (unit + (unit + (nat + unit))) 1
                     (Vector.cons Set (unit + (unit + (nat + unit))) 0 (Vector.nil Set)))).
  eexists (nat * ty_v + (unit + (nat * ty_v * (unit + (unit + (nat + unit))) * nat + (nat * ty_v * (unit + (unit + (nat + unit))) * nat * (unit + (unit + (nat + unit))) * nat + unit)))).
  eexists (?[F] ||| ?[G]).
  intro N.
  rewrite ex_correct.
  unfold ex_derive_parent.
  simpl.
  match goal with
    |- { init | equiv _ _ (_ _ _ ?s)} =>
    generalize s
  end.
  intros.
  let u := open_constr:(inl (N,f)) in
  eexists ?[init];
    unify ?init u.
  do 2 eexists.
  split.
  simpl.
  match goal with
    |- ?F _ = _ =>
    let u := open_constr:(fun '(N,f) => _) in
    unify F u
  end.
  simpl.
  apply eq_refl.

  match goal with
    |- equiv' _ ?s _ ?op =>
    let u := open_constr:(match N with
                          | O => _
                          | S N' => _
                          end)
    in
    unify s u;
    let u := open_constr:(match N with
                          | O => _
                          | S N' => _
                          end)
    in
    unify op u
  end.
  revert f.
  induction N; intros.
  simpl.
  econstructor.
  match goal with
    |- (_ ||| ?g) ?s = _ =>
    let u := open_constr:(inr (inl tt)) in
    unify s u;
      let u0 := open_constr:((fun _ => _)||| _) in
      unify g u0
  end.
  simpl.
  apply eq_refl.
  simpl.
  lazymatch goal with
    |- equiv' _ ?st (match ?z with _ => _ end) ?op =>
    let ty := type of st in
    let u := open_constr:(match z return ty with
                     | Some (s', Some (existT _ _ a)) => inr (inr (inl (N, f, s', a)))
                     | _ => inr (inr (inr (inr tt)))
                     end) in
    unify st u;
      let ty := type of op in
      let u := constr:(match z return ty with
                        | Some (s', Some (existT _ ef a)) => Some (existT args_effect putNat a)
                        | _ => None
                       end)
      in
      unify op u;
        destruct z
  end.
  destruct p.
  destruct o.
  destruct s0.
  econstructor.
  intros.
  simpl.
  match goal with
    |- ?g _ _ _ = _ =>
    let u := open_constr:((fun '(N, f, s, n) _ _ => _) ||| _) in
    unify g u
  end.
  simpl.
  match goal with
    |- _ = Some (?next _ _ , ?op _ _) =>
    let u := open_constr:(_ ||| (_ ||| ((fun '(N,f,s,n) r => _) ||| _))) in
    unify next u;
      let u := open_constr:(_ ||| (_ ||| ((fun '(N,f,s,n) r => _) ||| _))) in
      unify op u
  end.
  apply eq_refl.
  intros.
  simpl.
  lazymatch goal with
    |- equiv' _ ?st (match ?z with _ => _ end) ?op =>
    let ty := type of st in
    let u := constr:(match z return ty  with
                     | Some (s', Some (existT _ _ a)) => inr (inr (inr (inl (N, f, s, n, s', a))))
                     | _ => inr (inr (inr (inr tt)))
                          end)
    in
    unify st u;
      let u := constr:(match z with
                            | Some (_, Some (existT _ _ v)) => Some (existT args_effect putNat v)
                            | _ => None
                            end)
      in
      instantiate (1 := u);
        destruct z
  end.
  destruct p.
  destruct o.
  destruct s1.
  econstructor.
  intros.
  simpl.
  match goal with
    |- ?f _ _ _ = Some (?next _ _ , ?op _ _) =>
    let u := open_constr:(_ ||| _) in
    unify f u;
      let u := open_constr:(_ ||| (_ ||| (_ ||| ((fun x r => _) ||| _)))) in
      unify next u;
        let u := open_constr:(_ ||| (_ ||| (_ ||| ((fun x r => _) ||| _)))) in
        unify op u
  end.
  simpl.
  all: swap 1 2.
  intros.
  lazymatch goal with
    |- equiv' _ (?next _ _) _ _ =>
    let u0 := open_constr:(fun s r => _) in
    unify next u0
  end.
  simpl.
  apply IHN.
  clear IHN.
  match goal with
    |- ?g _ _ _ = ?rhs =>
    let u := open_constr:(fun '(N,f,s,n,s0,n0) _ _ => _) in
    unify g u
  end.
  simpl.
  lazymatch goal with
    |- _ = ?rhs =>
    instantiate (1 := rhs)
  end.
  apply eq_refl.
  econstructor.
  simpl.
  pattern_rhs tt.
  apply eq_refl.
  econstructor.
  simpl.
  auto.
  econstructor. auto.
  econstructor. auto.
  Grab Existential Variables.
  all: intros; (exact None || exact (inr (inl tt)) || idtac).
Defined.
