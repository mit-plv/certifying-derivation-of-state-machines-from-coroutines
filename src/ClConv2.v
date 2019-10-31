Require String Vector.
Require Import List FunctionalExtensionality.
Require Import StateMachines.Inhabit.
Import ListNotations.
Set Universe Polymorphism.
Open Scope type_scope.
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
      (forall r, equiv' step (next r) (p r) (op r)) ->
      (forall r, step s e r = Some (next r, op r)) ->
      equiv' step s (Eff a p) (Some (existT _ _ a))
  | Equiv'Done : forall s,
      step s = (fun _ _ => None) ->
      equiv' step s Done None.

  Definition equiv state (step : step_type state) init p :=
    exists op s, step init = (fun _ _ => Some (s, op)) /\ equiv' step s p op.

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

Definition equiv_coro A B state (step : step_type (fun _:yield_effect => A)(fun _:yield_effect => B) state) init p :=
  exists op s, forall r,
      step init yield r = Some (s r, op r) /\ equiv' step (s r) (p r) (op r).

Definition seqE A B (e : t (fun _:yield_effect => A) (fun _:yield_effect => B)) : (A -> (B -> t (fun _:yield_effect => A) (fun _:yield_effect => B)) -> t args_effect rets_effect) -> t args_effect rets_effect :=
  match e with
  | Done _ _ => fun _ => Done _ _
  | Eff _ a p => fun cont => cont a p
  end.

Notation "'const_yield' A" :=
  (fun _:yield_effect => A)
    (at level 10).

Definition coro_type A B state (_ : step_type (const_yield A) (const_yield B) state):= B -> t (const_yield A)(const_yield B).

Definition proc_coro A B state (step : step_type (const_yield A)(const_yield B) state)(c : coro_type step) (x : B) : (A -> coro_type step -> t args_effect rets_effect) -> t args_effect rets_effect :=
  seqE (c x).

Definition Let_coroutine A B
           (c : B -> t (fun _:yield_effect => A)(fun _:yield_effect => B)) p
  : t args_effect rets_effect :=
  p c.
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
  (proc_coro c x (fun n c => e))
    (at level 100, right associativity).
Notation "v1 <- 'yield' v2 ; e" :=
  (Eff yield v2 (fun v1 => e))
    (at level 100, right associativity).

Definition get_put : t args_effect rets_effect :=
  n <- getN;
  putN (S n);
    Done _ _.

Definition seqE' A state (x : option (state * option { e : yield_effect & A })) (f : state -> A -> t args_effect rets_effect)(f0 : t args_effect rets_effect) :=
  match x with
  | Some (s, Some (existT _ _ v)) => f s v
  | _ => f0
  end.

Fixpoint fin_prod n : Vector.t Type n -> Type :=
  match n as n0 return Vector.t Type n0 -> Type with
  | O => fun _ => unit
  | S n' =>
    fun types => Vector.caseS' types _ (fun t rest => fin_prod rest * t)
  end.

Fixpoint nth_fp n (types : Vector.t Type n)(v : fin_prod types) k : Vector.nth types k :=
  match k in Fin.t m
        return forall (types : Vector.t Type m),
      fin_prod types -> Vector.nth types k with
  | @Fin.F1 m =>
    fun (types : Vector.t Type (S m)) =>
      Vector.caseS' types
                    (fun types => fin_prod types -> Vector.nth types Fin.F1)
                    (fun t ts =>
                       fun v : fin_prod (Vector.cons _ t _ ts) => snd v)
  | @Fin.FS m k' =>
    fun (types : Vector.t Type (S m)) =>
      Vector.caseS' types
                    (fun types => fin_prod types -> Vector.nth types (Fin.FS k'))
                    (fun t ts =>
                       fun v : fin_prod (Vector.cons _ t _ ts) => nth_fp ts (fst v) k')
  end types v.

Fixpoint replace_fp n (types : Vector.t Type n)(v : fin_prod types) k (a0 : Vector.nth types k) : fin_prod types :=
  match k in Fin.t m return
        forall types : Vector.t Type m,
          fin_prod types -> Vector.nth types k -> fin_prod types
  with
  | @Fin.F1 m =>
    fun types : Vector.t Type (S m) =>
      Vector.caseS' types
                    (fun types => fin_prod types -> Vector.nth types Fin.F1 -> fin_prod types)
                    (fun t ts v a0 => (fst v, a0))
  | @Fin.FS m k' =>
    fun types : Vector.t Type (S m) =>
      Vector.caseS' types
                    (fun types => fin_prod types -> Vector.nth types (Fin.FS k') -> fin_prod types)
                    (fun t ts v a0 => (replace_fp ts (fst v) k' a0, snd v))
  end types v a0.

Inductive equiv_parent A B :
  forall n (states : Vector.t Type n),
    (forall k, step_type (fun _:yield_effect => A) (fun _:yield_effect => B) (Vector.nth states k)) ->
    (Vector.t (B -> t (fun _:yield_effect => A)(fun _:yield_effect => B)) n -> t args_effect rets_effect) ->
    (fin_prod states -> t args_effect rets_effect) ->
    Prop :=
| EPDone : forall n states
                  (steps : forall k : Fin.t n, step_type (fun _:yield_effect => A) (fun _:yield_effect => B) (Vector.nth states k)),
    equiv_parent _ steps (fun _ => Done _ _) (fun _ => Done _ _)
| EPEff : forall n states
                 (steps : forall k : Fin.t n, step_type (fun _:yield_effect => A) (fun _:yield_effect => B)(Vector.nth states k))
                 e a f g,
    (forall r, equiv_parent _ steps (fun cs => f cs r) (fun ss => g ss r)) ->
    equiv_parent _ steps (fun cs => Eff e a (f cs)) (fun ss => Eff e a (g ss))
| EPSeq :forall n states x k f f' g
                (steps : forall k : Fin.t n, step_type (fun _:yield_effect => A) (fun _:yield_effect => B) (Vector.nth states k)),
    (forall v cs c, f' cs v c = f v (Vector.replace cs k c)) ->
    (forall v, @equiv_parent _ _ n states steps (f v) (g v)) ->
    equiv_parent _ steps
        (fun cs => seqE (Vector.nth cs k x) (f' cs))
        (fun ss =>
           seqE' (steps k (nth_fp _ ss k) yield x) (fun s' v => g v (replace_fp _ ss k s')) (Done _ _))
| EPSpawn :
    forall n c f f' x state' states
           (steps : forall k : Fin.t n, step_type (fun _:yield_effect => A) (fun _:yield_effect => B) (Vector.nth states k))
           (step : step_type (fun _:yield_effect => A) (fun _:yield_effect => B) state') init g,
      equiv step init (c x) ->
      (forall v cs c, f' cs v c = f v (Vector.cons _ c _  cs)) ->
      (forall v,
          equiv_parent _ (fun k : Fin.t (S n) =>
                          Fin.caseS' k (fun k => step_type (fun _:yield_effect => A)(fun _:yield_effect => B) (Vector.nth (Vector.cons _ state' _ states) k)) step (fun k' => steps k'))
                       (f v)
                       (g v)) ->
    equiv_parent _ steps
        (fun cs => seqE (c x) (f' cs))
        (fun ss =>
           seqE' (step init yield x) (fun s' v => g v (ss, s')) (Done _ _))
| EPSpawnLet :
    forall n (c : B -> t (fun _:yield_effect => A)(fun _:yield_effect => B)) f f' state' states
           (steps : forall k : Fin.t n, step_type (fun _:yield_effect => A) (fun _:yield_effect => B) (Vector.nth states k))
           (step : step_type (fun _:yield_effect => A) (fun _:yield_effect => B) state') init g,
      equiv_coro step init c ->
      (forall cs c0, f' cs c0 = f (Vector.cons _ c0 _ cs)) ->
      (equiv_parent _ (fun k : Fin.t (S n) =>
                         Fin.caseS' k (fun k => step_type (fun _:yield_effect => A)(fun _:yield_effect => B)(Vector.nth (Vector.cons _ state' _ states) k)) step (fun k' => steps k'))
                    f
                    g) ->
      equiv_parent _ steps
                   (fun cs => Let_coroutine c (f' cs))
                   (fun ss  => g (ss, init)).


Lemma equiv_parent_sum :
  forall A B C D n (states : Vector.t Type n) fa fb ga gb steps (x : A + B),
    (forall a, equiv_parent states steps (fun cs => fa cs a) (fun ss => ga ss a)) ->
    (forall b, equiv_parent states steps (fun cs => fb cs b) (fun ss => gb ss b)) ->
    @equiv_parent C D n states steps
                  (fun cs => match x with
                             | inl a => fa cs a
                             | inr b => fb cs b
                             end)
                  (fun ss => match x with
                             | inl a => ga ss a
                             | inr b => gb ss b
                             end).
Proof.
  intros.
  destruct x; auto.
Qed.

Lemma equiv_parent_nat_rect :
  forall A B n (states : Vector.t Type n) X Y f f0 g g0 steps
         (x : Vector.t (B -> t (fun _:yield_effect => A)(fun _:yield_effect => B)) n -> X)
         (y : fin_prod states -> Y) N,
    (forall x y, @equiv_parent A B n states steps (fun cs => f cs (x cs)) (fun ss => g ss (y ss))) ->
    (forall N,
        (forall x y, @equiv_parent A B n states steps
                      (fun cs => nat_rect (fun X => _) (f cs) (f0 cs) N (x cs))
                      (fun ss => nat_rect (fun Y => _) (g ss) (g0 ss) N (y ss))) ->
        (forall x y,
            equiv_parent _ steps
                         (fun cs => nat_rect _ (f cs) (f0 cs) (S N) (x cs))
                         (fun ss => nat_rect _ (g ss) (g0 ss) (S N) (y ss)))) ->
  @equiv_parent A B n states steps
               (fun cs => nat_rect _ (f cs) (f0 cs) N (x cs))
               (fun ss => nat_rect _ (g ss) (g0 ss) N (y ss)).
Proof.
  intros.
  revert x y.
  induction N; intros; (auto || simpl; auto).
Qed.

Lemma equiv_parent_nat_rect_dep :
  forall A B N n (states : Vector.t Type n) X Y f f0 g g0 steps
         (x : Vector.t (B -> t (fun _:yield_effect => A)(fun _:yield_effect => B)) n -> X)
         (y : fin_prod states -> Y),
    (forall x y, @equiv_parent A B n states steps (fun cs => f cs (x cs)) (fun ss => g ss (y ss))) ->
    (forall N,
        (forall x y, @equiv_parent A B n states steps
                      (fun cs => nat_rect (fun X => _) (f cs) (f0 cs) N (x cs))
                      (fun ss => nat_rect (fun Y => _) (g ss) (g0 ss) N (y ss))) ->
        (forall x y,
            equiv_parent _ steps
                         (fun cs => nat_rect _ (f cs) (f0 cs) (S N) (x cs))
                         (fun ss => nat_rect _ (g ss) (g0 ss) (S N) (y ss)))) ->
  @equiv_parent A B n states steps
               (fun cs => nat_rect _ (f cs) (f0 cs) N (x cs))
               (fun ss => nat_rect _ (g ss) (g0 ss) N (y ss)).
Proof.
  intros.
  revert x y.
  induction N; intros; (auto || simpl; auto).
Qed.

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

Definition prod_curry_rev (A B C : Type)(f : A -> B -> C)(x : B * A) :=
  let (b,a) := x in
  f a b.

Ltac curry_lhs' :=
  lazymatch goal with
    |- ?x = _ =>
    let rec aux p :=
        lazymatch p with
        | ?f (_,_) =>
          let f' := open_constr:(prod_curry_rev (fun _ => _)) in
          unify f f'; unfold prod_curry_rev
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
    |- _ ?r = _ =>
    pattern_rhs r; apply equal_f
  end;
  repeat curry_lhs';
  lazymatch goal with
    |- ?f ?b ?arg = ?X =>
    lazymatch arg with
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
      pattern_rhs yield; apply equal_f;
      pattern_rhs b; apply equal_f
    end
  | _ => idtac
  end;
  simpl; apply eq_refl.

Ltac free_var body vars :=
  lazymatch vars with
  | (?rest,?a) =>
    let r := free_var body rest in
    lazymatch body with
    | context [a] =>
      constr:((r,a))
    | _ => r
    end
  | ?a => tt
  end.

Ltac derive_yield ptr env :=
  lazymatch goal with
    |- equiv' ?step ?st ?prog ?op =>
    lazymatch prog with
    | Eff _ ?a ?p =>
      lazymatch st with
      | ?f ?r =>
        let fv := free_var prog env in
        let u := open_constr:(fun r => _) in
        unify f u;
        lazymatch op with
        | ?g _ =>
          let u := open_constr:(fun r => _) in
          unify g u
        end;
        simpl;
        lazymatch goal with
          |- equiv' _ ?st' _ _ =>
          let u := open_constr:(ptr (inl fv)) in
          unify st' u
        end;
        eapply Equiv'Eff;
        [ let fr := fresh in
          intro fr;
          derive_yield (fun x => ptr (inr x)) (env,fr)
        | intros; simpl; dest_step
        ]
      | _ =>
        let fv := free_var prog env in
        let u := open_constr:(ptr (inl fv)) in
        unify st u;
        eapply Equiv'Eff;
        [ let fr := fresh in
          intro fr;
          derive_yield (fun x => ptr (inr x)) (env,fr)
        | intros; simpl; dest_step
        ]
      end
    | Done _ _ =>
      lazymatch st with
      | ?f ?r =>
        let fv := free_var prog (env,r) in
        let u := open_constr:(fun r => _) in
        unify f u;
        lazymatch op with
        | ?g _ =>
          let u := open_constr:(fun r => _) in
          unify g u
        end;
        simpl;
        lazymatch goal with
          |- equiv' _ ?st' _ _ =>
          let u := open_constr:(ptr fv) in
          unify st' u
        end;
        eapply Equiv'Done;
        simpl;
        repeat (dest_sum; simpl);
        lazymatch goal with
          |- ?f _ = _ =>
          let u := open_constr:(fun _ => _) in
          unify f u;
          simpl;
          apply eq_refl
        end
      end
    end
  end.

Ltac derive_child env :=
  match goal with
    |- _ _ ?init _ =>
    let u := open_constr:(inl env) in
    unify init u
  end;
  do 2 eexists;
  split;
  [ dest_step
  | derive_yield open_constr:(fun x => inr x) env].

Definition get_put_derive :
  {state & {step & {init | @equiv _ _ _ state step init get_put}}}.
Proof.
  unfold get_put.
  do 3 eexists.
  derive_child tt.
Defined.

Definition get_put2 : t args_effect rets_effect :=
  n <- getN;
    m <- getN;
  putN (S n);
  Done _ _.

Definition vec_curry A B n (f : A -> Vector.t A n -> B) : Vector.t A (S n) -> B :=
  fun v => Vector.caseS' v _ (fun a v0 => f a v0).

Lemma nth_tl : forall A n (v : Vector.t A (S n)) k,
    Vector.nth (Vector.tl v) k = Vector.nth v (Fin.FS k).
Proof.
  intros.
  apply (Vector.caseS' v).
  intros.
  reflexivity.
Qed.

Lemma nth_FS : forall A n (v : Vector.t A n) c k,
    Vector.nth (Vector.cons _ c _ v) (Fin.FS k) = Vector.nth v k.
Proof.
  auto.
Qed.

Lemma nth_replace : forall A n (v : Vector.t A n) c k,
    Vector.nth (Vector.replace v k c) k = c.
Proof.
  intros.
  revert v.
  induction k; intros;
  apply (Vector.caseS' v); auto.
Qed.

Lemma nth_replace_other : forall A n (v : Vector.t A n) c k k',
    k <> k' ->
    Vector.nth (Vector.replace v k c) k' = Vector.nth v k'.
Proof.
  intros.
  revert H v.
  apply (Fin.rect2 (fun n k k' =>
                      k <> k' ->
                      forall v : Vector.t A n,
                        Vector.nth (Vector.replace v k c) k' = Vector.nth v k'));
    intros.
  congruence.
  apply (Vector.caseS' v).
  auto.
  apply (Vector.caseS' v).
  auto.
  apply (Vector.caseS' v).
  intros.
  simpl.
  apply H.
  congruence.
Qed.

Lemma nth_replace_fp : forall n (types: Vector.t Type n) (fp: fin_prod types) k c,
    nth_fp _ (replace_fp _ fp k c) k = c.
Proof.
  intros.
  revert fp.
  induction k; intros.
  revert c fp.
  apply (Vector.caseS' types); intros.
  simpl in *.
  destruct fp.
  auto.
  revert c fp.
  apply (Vector.caseS' types); intros.
  simpl in *.
  destruct fp.
  auto.
Qed.

Lemma nth_replace_fp_other : forall n (types: Vector.t Type n) (fp: fin_prod types) k k0 c,
    k <> k0 ->
    nth_fp _ (replace_fp _ fp k c) k0 = nth_fp _ fp k0.
Proof.
  intros n types fp k k0.
  revert types fp.
  apply (Fin.rect2 (fun n k k0 =>
                      forall types fp (c : Vector.nth types k),
                        k <> k0 -> nth_fp _ (replace_fp _ fp k c) k0 = nth_fp _ fp k0)).
  congruence.
  intros n0 f types.
  apply (Vector.caseS' types); intros.
  simpl in fp.
  destruct fp.
  auto.
  intros n0 f types.
  apply (Vector.caseS' types); intros.
  simpl in fp.
  destruct fp.
  auto.
  intros n0 f g H types.
  apply (Vector.caseS' types); intros.
  simpl in fp.
  destruct fp.
  simpl.
  apply H.
  congruence.
Qed.

Ltac vec_replace v :=
  let vec := fresh in
  set (vec := v);
  lazymatch v with
  | Vector.replace ?v' ?k ?c =>
    replace c with (Vector.nth vec k) by (unfold vec; rewrite nth_replace; auto);
    lazymatch goal with
    | |- context[Vector.nth v' k] =>
      fail 0
    | |- context[Vector.nth v' ?k'] =>
      replace (Vector.nth v' k') with (Vector.nth vec k') by
          (unfold vec; rewrite nth_replace_other; congruence)
    | _ => idtac
    end
  | _ =>
    lazymatch type of v with
    | Vector.t _ (S ?n) =>
      let rec aux v k := (
            lazymatch v with
            | Vector.cons _ ?c _ ?cs =>
              replace c with (Vector.nth vec k) by (unfold vec; auto);
              aux cs (Fin.FS k)
            | Vector.nil => idtac
            | _ =>
              lazymatch goal with
                |- context[Vector.nth v ?m] =>
                let s := fresh in
                evar (s : Fin.t (S n));
                replace (Vector.nth v m) with (Vector.nth vec s) by
                    (unfold s, vec; etransitivity;
                     [repeat apply nth_FS|reflexivity])
              | _ => idtac
              end
            end)
      in
      aux v (@Fin.F1 n)
    end
  end.

Ltac prog_eq :=
  lazymatch goal with
    |- _ = ?f _ ?ccs =>
    vec_replace ccs;
    let u := open_constr:(fun v ccs0 => _) in
    unify f u;
    apply eq_refl
  | |- _ = ?f ?ccs =>
    vec_replace ccs;
    let u := open_constr:(fun ccs0 => _) in
    unify f u;
    apply eq_refl
  end.

Ltac derive_parent_core :=
  (lazymatch goal with
  | |- _ (?g _) =>
    let u := open_constr:(fun v0 => _) in
    unify g u
  | |- _ (fun ss => ?x ss _) =>
    let u := open_constr:(fun ss r => _) in
    unify x u
  | _ => idtac
  end;
  cbv beta;
  econstructor || eapply (EPEff putNat)) || econstructor.


Definition nat_rect_sig A (P : nat -> A -> Prop) (f0 : A) :
    P 0 f0 ->
    (forall n hn, { hSn | P n hn -> P (S n) hSn }) ->
    forall n, { h | P n h }.
Proof.
  intros.
  refine (exist _ (nat_rect _ f0 (fun m rec => proj1_sig (X m rec)) n) _).
  induction n.
  auto.
  simpl.
  destruct (X n (nat_rect (fun _ : nat => A) f0
             (fun (m : nat) (rec : A) => proj1_sig (X m rec)) n)).
  simpl.
  auto.
Defined.


Definition ex_coroutine k n : t (fun _:yield_effect => nat) (fun _:yield_effect => nat):=
  m <- yield (k + n)%nat;
    _ <- yield (n + m)%nat;
    Done _ _.

(*
Definition ex N :=
  let c1 := ex_coroutine 2 in
  let c2 := ex_coroutine 3 in
  n1 <- resume c1 $ 1;
    n2 <- resume c2 $ 2;
    nat_rect _ (fun _ _ => Done args_effect rets_effect)
             (fun N' rec c1 c2 =>
                m1 <- resume c1 $ n1;
                  putN m1;
                  m2 <- resume c2 $ n2;
                  putN m2;
                  rec c1 c2) N c1 c2.
*)
  
Ltac derive_parent_fix :=
  lazymatch goal with
    |- _ (?g _) =>
    let u := open_constr:(fun v0 => _) in
    unify g u
  end;
  cbv beta;
  lazymatch goal with
  | |- _ (fun ccs => nat_rect _ _ _ ?N _ _) _ =>
    lazymatch goal with
      |- _ ?g =>
      pattern N, g
    end;
    lazymatch goal with
      |- ?G _ ?g =>
      let e := fresh in
      unshelve (evar (e : {h | G N h});
                eassert (E := e : {h | G N h}));
      [|
       simpl;
       let e0 := fresh in
       pose (proj2_sig e) as e0;
       unfold e in e0;
       simpl in e0;
       apply e0
      ]
    end;
    eapply (nat_rect_sig _ _); simpl
  end.

Ltac solve_child :=
  match goal with
    |- equiv _ _ ?x =>
    let y := eval red in x in
        change x with y
  end;
  derive_child tt.

Ltac derive_parent :=
  intros;
  progress derive_parent_core
  || (lazymatch goal with
        |- _ (fun ss => ?X ss _) =>
        let u := open_constr:(fun ss r0 => _) in
        unify X u
      end;
      cbv beta;
      repeat lazymatch goal with
             | H : equiv_parent _ _ _ _ |- _ => apply H
             end)
  || derive_parent_fix
  || eapply equiv_parent_sum
  || prog_eq.

Lemma ex_coroutine_derive k n :
  { state & { step & { init | @equiv  _ _ _ state step init (ex_coroutine k n) }}}.
Proof.
  eexists.
  eexists.
  eexists.
  solve_child.
Defined.

(*
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
  repeat (eapply (proj2_sig (projT2 (projT2 (ex_coroutine_derive _ _)))) || derive_parent).
Defined.
Eval simpl in (fun N => proj1_sig (ex_derive_parent N)).

Transparent seqE.
*)

Lemma equiv_parent_eq_general : forall A B n states steps f g,
    @equiv_parent A B n states steps f g ->
    forall cs ss,
      (forall k x next op,
          steps k (nth_fp _ ss k) yield x = Some (next, op) ->
          equiv' (steps k) next (Vector.nth cs k x) op) ->
      (forall k x,
          steps k (nth_fp _ ss k) yield x = None ->
          Vector.nth cs k x = Done _ _) ->
      f cs = g ss.
Proof.
  intros A B n states steps f g H.
  induction H; intros; simpl.
  auto.
  f_equal.
  extensionality r.
  auto.
  destruct (steps k (nth_fp _ ss k) yield x) eqn:?.
  simpl.
  destruct p.
  destruct o.
  destruct s.
  apply H2 in Heqo.
  inversion Heqo.
  subst.
  simpl.
  rewrite H.
  apply H1.
  intros.
  destruct (Fin.eq_dec k0 k).
  subst.
  rewrite nth_replace.
  rewrite nth_replace_fp in H5.
  destruct x0.
  rewrite H9 in H5.
  inversion H5.
  subst.
  auto.
  rewrite nth_replace_other by auto.
  rewrite nth_replace_fp_other in H5 by auto.
  destruct x0.
  auto.
  intros.
  destruct x0.
  destruct (Fin.eq_dec k0 k).
  subst.
  rewrite nth_replace_fp in H5.
  rewrite H9 in H5.
  congruence.
  rewrite nth_replace_fp_other in H5 by auto.
  rewrite nth_replace_other by auto.
  auto.
  apply H2 in Heqo.
  inversion Heqo.
  auto.
  simpl.
  rewrite H3.
  simpl.
  auto.
  auto.
  simpl.
  destruct H.
  destruct H.
  destruct H.
  rewrite H.
  simpl.
  destruct x0.
  destruct s.
  inversion H5.
  subst.
  simpl.
  rewrite H0.
  apply H2.
  intros k x2.
  pattern k.
  apply Fin.caseS'.
  intros.
  simpl in *.
  destruct x0.
  rewrite H11 in H7.
  inversion H7.
  subst.
  auto.
  intros.
  simpl in *.
  auto.
  intros k x2.
  pattern k.
  apply Fin.caseS'; simpl; intros.
  destruct x0.
  rewrite H11 in H7.
  congruence.
  auto.
  inversion H5.
  subst.
  simpl.
  auto.
  unfold Let_coroutine.
  rewrite H0.
  apply IHequiv_parent.
  intro k.
  pattern k.
  apply Fin.caseS'; simpl; intros.
  destruct H as (op0,(s,(H5,H6))).
  rewrite H5 in H4.
  assert (op0 x = op) by congruence; assert (s x = next) by congruence; subst.
  auto.
  auto.
  intro k.
  pattern k.
  apply Fin.caseS'; simpl; intros.
  destruct H as (op0,(s,(H5,H6))).
  rewrite H5 in H4.
  congruence.
  auto.
Qed.

Lemma equiv_parent_eq : forall A B states steps f g cs ss,
    @equiv_parent A B 0 states steps f g ->
    f cs = g ss.
Proof.
  intros.
  eapply equiv_parent_eq_general.
  apply H.
  intro k.
  pattern k.
  apply Fin.case0.
  intro k.
  pattern k.
  apply Fin.case0.
Qed.

Ltac my_instantiate ev t :=
  let H := fresh in
  pose ev as H;
  instantiate (1 := t) in (Value of H);
  subst H.

Ltac st_op_to_ev :=
  lazymatch goal with
    |- equiv' ?step ?st ?prog ?op =>
    lazymatch st with
    | ?f _ =>
      let u := open_constr:(fun r => _) in
      unify f u;
      lazymatch op with
      | ?g _ =>
        let u := open_constr:(fun r => _) in
        unify g u
      end
    | ?f _ _ =>
      let u := open_constr:(fun r c => _) in
      unify f u;
      lazymatch op with
      | ?g _ _ =>
        let u := open_constr:(fun r c => _) in
        unify g u
      end
    | _ => idtac
    end;
    cbv beta
  end.

(*
Theorem ex_correct : forall N,
    ex N = proj1_sig (ex_derive_parent N) tt.
Proof.
  intros.
  set (x := fun _ => ex N).
  replace (ex N) with (x (Vector.nil _)); subst x.
  erewrite equiv_parent_eq.
  2: apply (proj2_sig (ex_derive_parent N)).
  reflexivity.
  auto.
Qed.
 *)

Lemma derive_parent_rect : forall state A N a0 f f0 st0 stS op0 opS step,
    (forall a, equiv' step (st0 a) (nat_rect (fun n => A -> _) (f a) (f0 a) 0 a) (op0 a)) ->
    (forall N0,
        (forall a, equiv' step (match N0 with O => st0 a | S N0' => stS a N0' end) (nat_rect _ (f a) (f0 a) N0 a) (match N0 with O => op0 a | S N0' => opS a N0' end)) ->
        (forall a, equiv' step (stS a N0)
                          (f0 a N0
                              (nat_rect
                                    (fun n : nat => A -> _) (f a) (f0 a)
                                    N0) a) (opS a N0))) ->
    @equiv' _ _ _ state step (match N with O => st0 a0 | S N0 => stS a0 N0 end) (nat_rect (fun n => A -> t args_effect rets_effect) (f a0) (f0 a0) N a0) (match N with O => op0 a0 | S N0 => opS a0 N0 end).
Proof.
  intros.
  revert a0.
  induction N; intros; auto.
  simpl.
  apply H0.
  intros.
  apply IHN.
Qed.

Lemma derive_sum : forall eff args rets A B state (x : A + B) fa fb sta stb opa opb step,
    (forall a, equiv' step (sta a) (fa a) (opa a)) ->
    (forall b, equiv' step (stb b) (fb b) (opb b)) ->
    @equiv' eff args rets state step (match x with
                              | inl a => sta a
                              | inr b => stb b
                              end)
            (match x with
             | inl a => fa a
             | inr b => fb b
             end)
            (match x with
             | inl a => opa a
             | inr b => opb b
             end).
Proof.
  intros.
  destruct x; auto.
Qed.

Lemma derive_seqE' : forall A state state' (x : option (state' * option { _ : yield_effect & A })) f f0 g g0 h h0 step,
    (forall s v, equiv' step (g s v) (f s v) (h s v)) ->
    equiv' step g0 f0 h0 ->
    @equiv' _ _ _ state step
            (match x with
             | Some (s, Some (existT _ _ v)) => g s v
             | _ => g0
             end) (seqE' x f f0)
            (match x with
             | Some (s, Some (existT _ _ v)) => h s v
             | _ => h0
             end).
Proof.
  intros.
  destruct x.
  destruct p.
  destruct o.
  destruct s0.
  simpl.
  auto.
  simpl.
  auto.
  simpl.
  auto.
Qed.

Lemma equal_f_dep : forall A (T : A -> Type) B (f g : forall a, T a -> B) a0,
    f = g -> f a0 = g a0.
Proof.
  intros.
  rewrite H.
  auto.
Qed.

Ltac next_ptr :=
  lazymatch goal with
    |- @equiv' _ _ _ ?st _ _ _ _ =>
    let rec aux state :=
        lazymatch state with
        | ?A + (?B + ?T) =>
          let f := aux T in
          open_constr:(fun x => @inr A _ (@inr B _ (f x)))
        | ?A + ?B => open_constr:(fun x => @inr A B x)
        | ?A => open_constr:(fun x:A => x)
        end
    in
    aux st
  end.

Ltac dest_step' :=
  lazymatch goal with
    |- @eq ?T (?g _ ?ef ?r) _ =>
    pattern_rhs r;
      apply equal_f;
      lazymatch goal with
        |- _ = ?rhs =>
        let tmp := fresh in
        lazymatch ef with
        | putNat =>
          set (tmp := (fun e => match e as e0 return rets_effect e0 -> T with
                                | putNat => rhs
                                | _ => fun _ => None
                                end) ef);
            replace rhs with tmp by (unfold tmp; auto);
            subst tmp
        | getNat =>
          set (tmp := (fun e => match e as e0 return rets_effect e0 -> T with
                                | getNat => rhs
                                | _ => fun _ => None
                                end) ef);
            replace rhs with tmp by (unfold tmp; auto);
            subst tmp
        | yield =>
          set (tmp := (fun _ => rhs) yield);
          replace rhs with tmp by (unfold tmp; auto);
          subst tmp
        end
      end;
      (apply equal_f_dep || apply equal_f);
      simpl;
      repeat (dest_sum; simpl);
      unify_fun
  end.

Ltac derive_core ptr env :=
  st_op_to_ev;
  lazymatch goal with
    |- equiv' _ _ ?prog _ =>
    let fv := free_var prog env in
    lazymatch prog with
    | Eff _ _ _ =>
      eapply (Equiv'Eff (ptr (inl fv)));
      [ let H := fresh in
        intro H;
        derive_core (fun x => ptr (inr x)) (env,H)
       | intros; simpl; dest_step']
    | Done _ _ =>
      eapply (Equiv'Done _ (ptr (inl fv)));
      simpl; dest_step
    | seqE' _ _ _ =>
      eapply (derive_seqE' _ (fun s v => _) (fun s v => _) (fun s v => _));
      [ let s := fresh in
        let v := fresh in
        intros s v;
        derive_core ptr (env,s,v)
       |]
    | (match ?x with _ => _ end) =>
      lazymatch type of x with
      | _ + _ =>
        eapply (derive_sum _ _ _ (fun a => _) (fun b => _) (fun a => _) (fun b => _));
        [ let a := fresh in
          intro a;
          simpl;
          let ptr := next_ptr in
          derive_core ptr (env,a)
        | let b := fresh in
          intro b;
          simpl;
          let ptr := next_ptr in
          derive_core ptr (env,b)
        ]
      end
    | nat_rect _ _ _ _ _ =>
      (now eauto)
      || (eapply (derive_parent_rect _ _ (fun a b => _) (fun a => _) (fun a => _));
          [ let a := fresh in
            intro a;
            simpl;
            let ptr := next_ptr in
            derive_core ptr (env,a)
          | let n := fresh in
            let H := fresh in
            let a := fresh in
            intros n H a;
            simpl;
            let ptr := next_ptr in
            derive_core ptr (env,n,a)
         ])
    end
  end.

Ltac derive_rec env :=
  let N := fresh in
  eexists;
  eexists;
  intro N;
  eexists ?[init];
  lazymatch goal with
    |- equiv _ _ ?prog =>
    let H := fresh in
    eassert (equiv_parent (Vector.nil Set)
                          (fun p : Fin.t 0 =>
                             Fin.case0
                               (fun k : Fin.t 0 =>
                                  step_type (fun _ : yield_effect => nat) (fun _ : yield_effect => nat)
                                            (Vector.nth (Vector.nil Set) k)) p)
                          (fun
                              _ : Vector.t
                                    (nat ->
                                     t (fun _ : yield_effect => nat) (fun _ : yield_effect => nat)) 0
                            => prog) _) as H by (repeat (solve_child || derive_parent));
    let tmp := fresh in
    eset (tmp := fun _: Vector.t _ 0 => prog);
      replace prog with (tmp (Vector.nil _)) by (unfold tmp; auto);
      subst tmp;
      erewrite equiv_parent_eq by (apply H)
  end;
  simpl;
  match goal with
    |- equiv _ _ (_ ?s) =>
    let u := open_constr:(inl (N,s)) in
    unify ?init u;
    generalize s
  end;
  intros;
  repeat eexists;
  [ dest_sum; simpl; unify_fun
  | derive_core open_constr:(fun x => inr x) tt;
    let ptr := next_ptr in
    eapply (Equiv'Done _ (ptr tt));
    simpl;
    apply eq_refl || (pattern_rhs tt; apply eq_refl)
  ].

Ltac derive_child' env :=
  lazymatch goal with
    |- equiv _ _ ?x =>
    let y := eval red in x in
        change x with y
  | |- equiv_coro _ _ ?x =>
    let y := eval red in x in
        change x with y
  | _ => idtac
  end;
  simpl;
  match goal with
    |- _ _ ?init _ =>
    let u := open_constr:(inl env) in
    unify init u
  end;
  repeat eexists;
  [ dest_sum; simpl; unify_fun
  | derive_core open_constr:(fun x => inr x) env
  ].

Lemma ex_coroutine_derive' :
  { state & { step & forall k, { init | @equiv_coro _ _ state step init (ex_coroutine k) }}}.
  do 3 eexists.
  lazymatch goal with
    |- equiv _ _ ?x =>
    let y := eval red in x in
        change x with y
  | |- equiv_coro _ _ ?x =>
    let y := eval red in x in
        change x with y
  end;
  simpl;
  match goal with
    |- _ _ ?init _ =>
    let u := open_constr:(inl (tt,k)) in
    unify init u
  end.
  repeat eexists.
  match goal with
    |- _ (@inl ?A ?B _) _ _ = _ (?s _, _) =>
    let u := open_constr:(_+_) in
    unify B u;
    let u := open_constr:(fun x => inr (inl (tt,k,x))) in
    unify s u
  end.
  all: swap 1 2.
  cbv beta.
  derive_core open_constr:(fun x => inr x) (tt,k,r).  
  simpl.
  pattern_rhs r.
  apply equal_f.
  pattern_rhs yield.
  apply equal_f.
  curry_lhs.
  unify_fun.
  Grab Existential Variables.
  2: exact unit.
  intros.
  exact None.
Defined.

Definition ex_coroutine_equiv k : equiv_coro _ _ (ex_coroutine k) :=
  proj2_sig (projT2 (projT2 ex_coroutine_derive') k).

Definition ex_coroutine_equiv' k
  : equiv_coro ltac:(let x := eval simpl in (projT1 (projT2 ex_coroutine_derive')) in exact x) ltac:(let x := eval simpl in (proj1_sig (projT2 (projT2 ex_coroutine_derive') k)) in exact x) (ex_coroutine k) :=
  ex_coroutine_equiv k.

Hint Resolve ex_coroutine_equiv ex_coroutine_equiv' : equivc.

(*
Theorem ex_derive :
  {state & {step & forall N, {init | @equiv _ _ _ state step init (ex N)}}}.
Proof.
  unshelve derive_rec tt;
    exact unit || exact tt.
Defined.

Eval cbv [prod_curry sum_merge ex_derive projT1 projT2] in projT1 (projT2 ex_derive).

Definition ex2_coroutine (fuel : nat) : nat + unit -> t (fun _:yield_effect => nat + unit) (fun _:yield_effect => nat + unit)  :=
  nat_rect _
           (fun _ _ => Done _ _)
           (fun fuel' rec accum i =>
              match i with
              | inl k => i' <- yield (inr tt);
                           rec (accum + k)%nat i'
              | inr _ => i' <- yield (inl accum); rec accum i'
              end)
           fuel 0.

Definition ex2 : t args_effect rets_effect :=
  let c := ex2_coroutine 5 in
  k <- getN;
    _ <- resume c $ (inl k);
    m <- getN;
    _ <- resume c $ (inl m);
    x <- resume c $ (inr tt);
    match x with
    | inl n => putN n; Done _ _
    | inr _ => Done _ _
    end.
*)

(*
Theorem ex2_derive_parent :
  {g | @equiv_parent _ _ 0 (Vector.nil _)
                               (fun p => Fin.case0 (fun k => step_type (fun _:yield_effect => nat + unit) (fun _:yield_effect => nat + unit) (Vector.nth _ k)) p)
                               (fun _ => ex2)
                               g}.
Proof.
  unfold ex2.
  eexists.
  unshelve (repeat (intros; (derive_child' tt || derive_parent)));
  exact (fun _ _ _ => None) ||
  exact unit.
Defined.
*)

Ltac derive env :=
  eexists;
  eexists;
  eexists (inl tt);
  lazymatch goal with
    |- equiv _ _ ?prog =>
    let H := fresh in
    eassert (@equiv_parent _ _ 0 (Vector.nil _)
                           (fun p => Fin.case0 (fun k => step_type (fun _:yield_effect => nat + unit) (fun _:yield_effect => nat + unit) (Vector.nth _ k)) p)
                           (fun _ => prog)
                           _) as H by
          (unshelve (repeat (intros; (derive_child' tt || derive_parent)));
           exact (fun _ _ _ => None) || exact unit);
    let tmp := fresh in
    eset (tmp := fun _: Vector.t _ 0 => prog);
      replace prog with (tmp (Vector.nil _)) by (unfold tmp; auto);
      subst tmp;
      erewrite equiv_parent_eq by (apply H)
  end;
  simpl;
  repeat eexists;
  [ dest_sum; simpl; unify_fun
  | derive_core open_constr:(fun x => inr x) tt;
    let ptr := next_ptr in
    eapply (Equiv'Done _ (ptr tt));
    simpl;
    apply eq_refl || (pattern_rhs tt; apply eq_refl)
  ].

(*
Theorem ex2_derive :
  { state & { step & { init | @equiv _ _ _ state step init ex2 } } }.
Proof.
  unshelve derive tt; simpl; intros; (exact None || exact unit || exact tt).
Defined.

Eval cbv in projT1 (projT2 ex2_derive).
 *)

Definition replace A i l (a:A) :=
  (fix aux i l pre :=
    match l with
    | [] => []
    | x::l' =>
      match i with
      | O => pre ++ a :: l'
      | S i' => aux i' l' (pre ++ [x])
      end
    end) i l [].

Definition pipe A B (a : A)(f : A -> B) := f a.


Definition option_branch A B (f : A -> B) f0 o :=
  match o with
  | None => f0
  | Some a => f a
  end.

Definition nat_rect_nondep A f (f0 : nat -> A -> A) :=
  fix F (n : nat) : A :=
    match n with
    | O => f
    | S n' => f0 n' (F n')
    end.

Instance coro_type_inhabitant A B state step :
  Inhabit (@coro_type A B state step) :=
  { inhabitant := fun _ => Done _ _ }.

Instance prod_inhabitant A B `{IA : Inhabit A} `{IB : Inhabit B} : Inhabit (A * B) :=
  { inhabitant := (inhabitant, inhabitant) }.

Instance unit_inhabitant : Inhabit unit := {inhabitant := tt }.

Instance sum_inhabitant A B `{IA : Inhabit A} : Inhabit (A + B) :=
  { inhabitant := inl inhabitant }.

Instance arrow_inhabitant A B `{IB : Inhabit B} : Inhabit (A -> B) :=
  { inhabitant := fun _:A => inhabitant }.

Instance option_inhabitant A : Inhabit (option A) :=
  { inhabitant := None }.

Instance t_inhabitant e a r : Inhabit (@t e a r) :=
  { inhabitant := Done _ _ }.

Definition seq_abs A B state (step : step_type (fun _:yield_effect => A)(fun _:yield_effect => B) state) (x:B) C (_:C) (g : A -> C -> t args_effect rets_effect) := t_inhabitant.

Definition step_state A B state (step : step_type (fun _:yield_effect => A)(fun _:yield_effect => B) state) st x g :=
  seqE' (step st yield x) (fun s v => g v s) (Done _ _).

Opaque dummy.

Definition K A B :=
  fun (x : A)(_ : B) => x.

Ltac get_init c :=
  let init := open_constr:(_) in
  let _ := constr:(ltac:(auto with equivc) : equiv_coro _ init c) in
  init.

Ltac to_dummy i p :=
  lazymatch p with
  | pipe ?c ?f =>
    let init := get_init c in
    let x := (eval cbv beta in (f (dummy _ _ i))) in
    let d := to_dummy (S i) x in
    lazymatch d with
    | context [dummy _ ?T i] =>
      lazymatch (eval pattern (dummy _ T i) in d) with
      | ?g _ =>
        constr:((pipe, init, g))
      end
    end
  | @Eff _ args_effect rets_effect ?e ?a ?f =>
    let x := (eval cbv beta in (f (dummy _ _ i))) in
    let d := to_dummy (S i) x in
    lazymatch (eval pattern (dummy _ (rets_effect e) i) in d) with
    | ?g _ =>
      constr:((@Eff _ args_effect rets_effect e a, g))
    end
  | @proc_coro ?A ?B ?state ?step ?c ?z ?f =>
    let x := (eval cbv beta in (f (dummy _ _ i) (dummy _ _ (S i)))) in
    lazymatch f with
    | context [proc_coro] =>
      let d := to_dummy (S (S i)) x in
      lazymatch type of f with
      | _ -> ?T -> _ =>
        lazymatch (eval pattern (dummy _ A i), (dummy _ T (S i)) in d) with
        | ?g _ _ =>
          constr:((@seq_abs A B state step z (coro_type step) c, g))
        end
      end
    | _ =>
      constr:((@seq_abs A B state step z (coro_type step) c, f))
    end
  | @option_branch ?A ?B ?f ?f0 ?o =>
    let x := (eval cbv beta in (f (dummy _ _ i))) in
    let d := to_dummy (S i) x in
    let d0 := to_dummy i f0 in
    lazymatch (eval pattern (dummy _ A i) in d) with
    | ?g _ =>
      constr:((@option_branch A B, g : A -> _, d0, o))
    end
  | @nat_rect_nondep ?A ?f ?f0 ?n ?a =>
    let x := (eval cbv beta in (f0 (dummy _ _ i) (dummy _ _ (S i)) (dummy _ _ (S (S i))))) in
    let y := (eval cbv beta in (f (dummy _ _ i))) in
    let d := to_dummy (S i) y in
    let d0 := to_dummy (S (S (S i))) x in
    let T := type of a in
    lazymatch (eval pattern (dummy _ nat i), (dummy _ A (S i)), (dummy _ T (S (S i))) in d0) with
    | ?g0 _ _ _ =>
      lazymatch (eval pattern (dummy _ T i) in d) with
      | ?g _ =>
        constr:((@nat_rect_nondep A, g, g0, n, a))
      end
    end
  | _ => p
  end.

Ltac reconstruct tree :=
  lazymatch tree with
  | (pipe, ?init, ?f) =>
    let x := (eval cbv beta in (f init)) in
    reconstruct x
  | (Eff ?e ?a, ?p) =>
    let x := (eval cbv beta in (p (dummy _ _ tt))) in
    let p' := reconstruct x in
    lazymatch type of p with
    | ?ty -> _ =>
      lazymatch (eval pattern (dummy _ ty tt) in p') with
      | ?p'' _ =>
        constr:(Eff e a p'')
      end
    end
  | (@seq_abs ?A ?B _ ?step ?z ?state ?st, ?p) =>
    let x := (eval cbv beta in (p (dummy _ _ tt) (dummy _ _ tt))) in
    let p' := reconstruct x in
    lazymatch (eval pattern (dummy _ A tt), (dummy _ state tt) in p') with
    | ?p'' _ _ =>
      constr:(@step_state A B _ step st z p'')
    end
  | (@option_branch ?A ?B, ?f, ?f0, ?o) =>
    let x := (eval cbv beta in (f (dummy _ _ tt))) in
    let p' := reconstruct x in
    lazymatch (eval pattern (dummy _ A tt) in p') with
    | ?p'' _ =>
      constr:(@option_branch A B p'' f0 o)
    end
  | (@nat_rect_nondep ?A, ?f, ?f0, ?n, ?a) =>
    let x := (eval cbv beta in (f (dummy _ _ tt))) in
    let y := (eval cbv beta in (f0 (dummy _ _ tt) (dummy _ _ tt) (dummy _ _ tt))) in
    let f' := reconstruct x in
    let f0' := reconstruct y in
    let ty := type of a in
    lazymatch (eval pattern (dummy _ ty tt) in f') with
    | ?f'' _ =>
      lazymatch (eval pattern (dummy _ nat tt), (dummy _ A tt), (dummy _ ty tt) in f0') with
      | ?f0'' _ _ _ =>
        constr:(@nat_rect_nondep A f'' f0'' n a)
      end
    end
  | _ => tree
  end.

Ltac coro_to_state p :=
  let x := to_dummy 0 p in
  lazymatch x with
  | context [@coro_type _ _ ?state ?step] =>
    lazymatch (eval pattern (coro_type step) in x) with
    | ?F _ =>
      let y := (eval cbv beta in (F state)) in
      reconstruct y
    end
  end.

(*
Definition take_nth n :=
  pipe (ex_coroutine 0 : coro_type (projT1 (projT2 ex_coroutine_derive')))
       (fun c0 =>
          pipe (ex_coroutine 1 : coro_type (projT1 (projT2 ex_coroutine_derive')))
               (fun c1 =>
                  nth_error [c0; c1] n)).


Goal nat -> True.
  intro n.
  let x := (eval red in (take_nth n)) in
  let x' := coro_to_state x in
  idtac x'.
Abort.


Definition take_nth_get (g : forall A, A -> t args_effect rets_effect) :=
  pipe (ex_coroutine 0 : coro_type (projT1 (projT2 ex_coroutine_derive')))
       (fun c0 =>
          n <- getN;
          pipe (ex_coroutine 1 : coro_type (projT1 (projT2 ex_coroutine_derive')))
               (fun c1 =>

                  g _ (nth_error [c0; c1] n))).

Goal (forall A, A -> t args_effect rets_effect) -> True.
  intro g.
  let x := (eval red in (take_nth_get g)) in
  let x' := coro_to_state x in
  idtac x'.
Abort.

Definition opt_nth (n:nat)(g : forall A, A  -> t args_effect rets_effect) :=
  pipe (ex_coroutine 0 : coro_type (projT1 (projT2 ex_coroutine_derive')))
       (fun c0 =>
          pipe (ex_coroutine 1 : coro_type (projT1 (projT2 ex_coroutine_derive')))
               (fun c1 =>
                  n <- getN;
                  option_branch
                    (fun c => g _ c)
                    (Done _ _)
                    (nth_error [c0; c1] n))).

Goal nat -> (forall A, A -> t args_effect rets_effect) -> True.
  intros n g.
  let x := (eval red in (opt_nth n g)) in
  let x' := coro_to_state x in
  idtac x'.
Abort.

*)

Definition proc_ex k :=
  pipe (ex_coroutine 0 : coro_type (projT1 (projT2 ex_coroutine_derive')))
       (fun c =>
          r <- resume c $ k;
            putN r; Done _ _).
Goal nat -> True.
  intro k.
  let x := (eval red in (proc_ex k)) in
  let x' := coro_to_state x in
  idtac x'.
Abort.

Definition opt_nth' (n:nat) :=
  pipe (ex_coroutine 0 : coro_type (projT1 (projT2 ex_coroutine_derive')))
       (fun c0 =>
          pipe (ex_coroutine 1 : coro_type (projT1 (projT2 ex_coroutine_derive')))
               (fun c1 =>
                  n <- getN;
                    option_branch
                      (fun c : @coro_type nat nat _ _ =>
                         r <- resume c $ 2;
                           putN r; Done _ _)
                      (Done _ _)
                      (nth_error [c0; c1] n))).

Goal nat -> True.
  intros n.
  let x := (eval red in (opt_nth' n)) in
  let x' := coro_to_state x in
  idtac x'.
Abort.

Fixpoint zip_list A1 A2 (l1 : list A1)(l2 : list A2) : option (list (A1 * A2)):=
  match l1, l2 with
  | [], [] => Some []
  | a1::l1', a2::l2' =>
    option_map (fun l => (a1,a2) :: l) (zip_list l1' l2')
  | _, _ => None
  end.

Class Foldable (F : Type -> Type) :=
  { foldr : forall A B, (A -> B -> B) -> B -> F A -> B;
    zip : forall A1 A2, F A1 -> F A2 -> option (F (A1 * A2));
    to_list : forall A, F A -> list A;
    to_list_foldr : forall A B (f : A -> B -> B) b x,
        foldr f b x = fold_right f b (to_list x);
    zip_to_list : forall A1 A2 (x1 : F A1)(x2 : F A2) x,
        zip x1 x2 = Some x -> Some (to_list x) = zip_list (to_list x1) (to_list x2)
  }.

Program Instance list_Foldable : Foldable list :=
  { foldr := fun A B => @fold_right B A;
    zip := zip_list;
    to_list := fun _ x => x
  }.

Definition size A F `{F_Foldable : Foldable F} (x : F A) : (nat : Type) :=
  foldr (fun _ accum => S accum) 0 x.

Definition nth_err A F `{F_Foldable : Foldable F}(x : F A) :=
  foldr (fun a p n =>
           match n with
           | O => Some a
           | S n' => p n'
           end)
        (fun _ => None) x.

Definition GenForall2 A1 A2 F `{F_Foldable : Foldable F}
           (R : A1 -> A2 -> Prop) (x1 : F A1) (x2 : F A2) :=
  exists x, zip _ _ x1 x2 = Some x /\ foldr (fun '(a1, a2) p => R a1 a2 /\ p) True x.

Lemma GenForall2_cons : forall A1 A2 (R : A1 -> A2 -> Prop) (x1 : list A1) (x2 : list A2) a1 a2,
    R a1 a2 ->
    GenForall2 R x1 x2 ->
    GenForall2 R (a1::x1) (a2::x2).
Proof.
  unfold GenForall2. simpl.
  intros.
  destruct H0 as (x,(H1,H2)).
  exists ((a1,a2) :: x).
  split.
  rewrite H1.
  auto.
  simpl.
  auto.
Qed.

Lemma nth_err_nth_error : forall A F (F_Foldable : Foldable F) (x : F A) n,
    nth_err _ x n = nth_error (to_list _ x) n.
Proof.
  intros.
  unfold nth_err.
  rewrite to_list_foldr.
  revert n.
  induction (to_list A x); intros; simpl.
  destruct n; auto.
  destruct n; simpl; auto.
Qed.

Lemma size_length : forall A F (F_Foldable : Foldable F) (x : F A),
    size _ x = length (to_list _ x).
Proof.
  intros.
  unfold size.
  rewrite to_list_foldr.
  induction (to_list _ x); simpl; auto.
Qed.

Lemma nth_err_Some : forall A (F : Type -> Type) (F_Foldable : Foldable F) (x : F A) n a,
    nth_err _ x n = Some a ->
    n < size _ x.
Proof.
  intros.
  unfold size, nth_err in *.
  rewrite to_list_foldr in *.
  revert n a H.
  induction (to_list _ x); simpl; intros.
  congruence.
  destruct n.
  auto with arith.
  apply -> PeanoNat.Nat.succ_lt_mono.
  eauto.
Qed.

Lemma nth_err_None : forall A F (F_Foldable : Foldable F) (x : F A) n,
    nth_err _ x n = None ->
    ~ n < size _ x.
Proof.
  intros.
  unfold size, nth_err in *.
  rewrite to_list_foldr in *.
  revert n H.
  induction (to_list _ x); simpl; intros.
  auto with arith.
  destruct n.
  congruence.
  apply IHl in H.
  auto with arith.
Qed.
(*
Lemma GenForall2_size : forall A1 A2 F (F_Foldable : Foldable F) R (x1 : F A1) (x2 : F A2),
    GenForall2 R x1 x2 -> size _ x1 = size _ x2.
Proof.
  intros.
  destruct H.
  auto.
Qed.
*)
Lemma GenForall2_Forall2 : forall A1 A2 F (F_Foldable : Foldable F) R (x1 : F A1) (x2 : F A2),
    GenForall2 R x1 x2 -> Forall2 R (to_list _ x1) (to_list _ x2).
Proof.
  intros.
  unfold GenForall2 in H.
  destruct H as (x,(H0,H1)).
  rewrite to_list_foldr in H1.
  apply zip_to_list in H0.
  generalize dependent (to_list _ x).
  generalize (to_list A2 x2).
  induction (to_list _ x1); intros.
  destruct l.
  auto.
  simpl in H0.
  congruence.
  destruct l0.
  simpl in H0.
  congruence.
  simpl in *.
  destruct (zip_list l l0) eqn:?.
  simpl in *.
  symmetry in Heqo.
  inversion H0. subst.
  simpl in H1.
  econstructor.
  tauto.
  apply IHl in Heqo.
  auto.
  tauto.
  simpl in H0.
  congruence.
Qed.

Lemma GenForall2_size : forall (A1 A2 : Type) (F : Type -> Type) (F_Foldable : Foldable F) R (x1 : F A1) (x2 : F A2),
    GenForall2 R x1 x2 ->
    size _ x1 = size _ x2.
Proof.
  intros.
  destruct H.
  destruct H.
  apply zip_to_list in H.
  unfold size.
  repeat rewrite to_list_foldr in *.
  generalize dependent (to_list _ x2).
  generalize dependent (to_list _ x).
  induction (to_list _ x1); simpl in *; intros.
  destruct l0; simpl in *; congruence.
  destruct l1; simpl in *.
  congruence.
  f_equal.
  destruct (zip_list l l1) eqn:?; simpl in *.
  apply (IHl l2).
  inversion H. subst.
  simpl in H0.
  tauto.
  inversion H. subst.
  auto.
  congruence.
Qed.

Lemma GenForall2_nth_Some_None : forall (A1 A2 : Type) (F : Type -> Type) (F_Foldable : Foldable F) R (x1 : F A1) (x2 : F A2) n a1,
    GenForall2 R x1 x2 ->
    nth_err _ x1 n = Some a1 ->
    nth_err _ x2 n = None ->
    False.
Proof.
  intros.
  apply nth_err_None in H1.
  apply nth_err_Some in H0.
  apply GenForall2_size in H.
  rewrite H in H0.
  auto.
Qed.

Lemma GenForall2_nth_None_Some : forall (A1 A2 : Type) (F : Type -> Type) (F_Foldable : Foldable F) R (x1 : F A1) (x2 : F A2) n a2,
    GenForall2 R x1 x2 ->
    nth_err _ x1 n = None ->
    nth_err _ x2 n = Some a2 ->
    False.
Proof.
  intros.
  apply nth_err_Some in H1.
  apply nth_err_None in H0.
  apply GenForall2_size in H.
  rewrite H in H0.
  auto.
Qed.

Lemma GenForall2_nth_Some : forall (A1 A2 : Type) (F : Type -> Type) (F_Foldable : Foldable F) R (x1 : F A1) (x2 : F A2) n a1 a2,
    GenForall2 R x1 x2 ->
    nth_err _ x1 n = Some a1 ->
    nth_err _ x2 n = Some a2 ->
    R a1 a2.
Proof.
  intros.
  unfold nth_err in *.
  unfold GenForall2 in H.
  destruct H.
  destruct H.
  unfold size in H.
  rewrite to_list_foldr in H2.
  rewrite to_list_foldr in H0.
  rewrite to_list_foldr in H1.
  apply zip_to_list in H.
  generalize dependent (to_list _ x2).
  generalize dependent (to_list _ x).
  revert n a1 a2 H0.
  induction (to_list _ x1); simpl in *; intros.
  destruct l0.
  inversion H. subst.
  simpl in H1.
  congruence.
  congruence.
  destruct l1; [congruence|].
  destruct (zip_list l l1) eqn:?; simpl in *; [|congruence].
  inversion H. subst.
  simpl in H2.
  destruct n.
  inversion H0. subst.
  inversion H1. subst.
  tauto.
  destruct H2.
  eapply IHl.
  eauto.
  eauto.
  symmetry. eauto.
  auto.
Qed.

Hint Resolve GenForall2_size nth_err_None nth_err_Some GenForall2_cons GenForall2_nth_None_Some GenForall2_nth_Some_None : foldable.
Transparent proc_coro.


Definition loop_ex (n i : nat)(g : forall A, A -> t args_effect rets_effect) :=
  pipe (ex_coroutine 0 : coro_type (projT1 (projT2 ex_coroutine_derive')))
       (fun c0 =>
          nat_rect_nondep
            (fun l => option_branch
                        (fun c => g _ c)
                        (Done _ _)
                        (nth_err _ l i))
            (fun m rec l =>
               pipe (ex_coroutine m : coro_type (projT1 (projT2 ex_coroutine_derive')))
                    (fun cm =>
                       rec (cm::l)))
            n [c0]).

Definition equiv_coro' A B `{IA : Inhabit A} `{IB : Inhabit B} state (step : step_type _ _ state) st (coro : B -> t (const_yield A) (const_yield B)) :=
  exists op, equiv' step st (r <- yield inhabitant; coro r) op.

Ltac get_step c :=
  let step := open_constr:(_) in
  let _ := constr:(ltac:(auto with equivc') : equiv_coro' step _ c) in
  step.

Ltac derive_child'' env :=
  lazymatch goal with
    |- equiv _ _ ?x =>
    let y := eval red in x in
        change x with y
  | |- equiv_coro' _ _ ?x =>
    let y := eval red in x in
        change x with y
  | _ => idtac
  end;
  simpl;
  match goal with
    |- _ _ ?init _ =>
    let u := open_constr:(inl env) in
    unify init u
  end;
  let r := fresh in
  repeat eexists; try econstructor;
  [ intro r; derive_core open_constr:(fun x => inr x) (env,r)
  | intros; dest_step'
  ].

Lemma ex_coroutine_derive'' :
  { state & { step & forall k, { init | @equiv_coro' _ _ _ _ state step init (ex_coroutine k) }}}.
  do 3 eexists.
  derive_child'' (tt,k).
  Grab Existential Variables.
  2: exact unit.
  intros.
  exact None.
Defined.

Definition ex_coroutine_equiv2 k : equiv_coro' _ _ (ex_coroutine k) :=
  proj2_sig (projT2 (projT2 ex_coroutine_derive'') k).

Definition ex_coroutine_equiv2' k
  : equiv_coro' ltac:(let x := eval simpl in (projT1 (projT2 ex_coroutine_derive'')) in exact x) ltac:(let x := eval simpl in (proj1_sig (projT2 (projT2 ex_coroutine_derive'') k)) in exact x) (ex_coroutine k) :=
  ex_coroutine_equiv2 k.

Hint Resolve ex_coroutine_equiv2 ex_coroutine_equiv2' : equivc.
Hint Resolve ex_coroutine_equiv2 : equivc'.

Lemma GenForall2_nth_Some_equiv_coro : forall A B (IA : Inhabit A) (IB : Inhabit B) state (step : step_type (const_yield A) (const_yield B) state) F (F_Foldable : Foldable F) x1 x2 n a1 a2,
    GenForall2 (fun (coro : coro_type step) (st : state) => equiv_coro' step st coro) x1 x2 ->
    nth_err _ x1 n = Some a1 ->
    nth_err _ x2 n = Some a2 ->
    equiv_coro' step a2 a1.
Proof.
  intros.
  eapply (GenForall2_nth_Some (R := (fun (coro : coro_type step) (st : state) => equiv_coro' step st coro))); eauto.
Qed.

Hint Resolve GenForall2_nth_Some_equiv_coro : foldable.

Ltac generalize_and_ind :=
  lazymatch goal with
    |- nat_rect_nondep ?A _ ?k ?l = nat_rect_nondep _ _ _ ?l' =>
    lazymatch type of l with
    | context [@coro_type _ _ ?state ?step] =>
        cut (GenForall2 (fun (coro : coro_type step) (st : state) => equiv_coro' step st coro) l l');
      [ generalize l l'
       |unfold GenForall2; eexists; split; [reflexivity|simpl; eauto with equivc]];
      induction k; intros; unfold nat_rect_nondep
    end
  end.


Ltac proc_step :=
  lazymatch goal with
    |- proc_coro ?c ?x ?f = step_state ?step ?st _ ?g =>
    let H := fresh in
    let H0 := fresh in
    assert (equiv_coro' step st c) as (H,H0);
    [eauto with foldable
    |
    let s := fresh "s" in
    let e := fresh "e" in
    let a := fresh "a" in
    let p := fresh "p" in
    let next := fresh "next" in
    let op := fresh "op" in
    let H1 := fresh in
    let H2 := fresh in
    inversion H0 as [s e a p next op H1 H2|]; subst;
    unfold step_state at 1, seqE' at 1;
    rewrite H2;
    lazymatch goal with
      |- context [match op ?x with _ => _ end] =>
      specialize (H1 x);
      destruct (op x);
      inversion H1; subst;
      unfold proc_coro at 1, seqE at 1;
      lazymatch goal with
        H_ : _ = c x |- _ =>
        rewrite <- H_
      end
    end
    ]
  end.

Ltac dest_opt :=
  lazymatch goal with
    |- option_branch _ _ ?o = option_branch _ _ ?o0 =>
    destruct o eqn:?, o0 eqn:?;
             unfold option_branch
  end.

(*
Notation "'let_coro' x := c 'in' p" :=
  (pipe (c : coro_type ltac:(let step := get_step c in exact step))
        (fun x => p))
    (at level 200, only parsing).
*)

Definition loop_ex' (n i : nat) :=
  pipe (ex_coroutine 0 : coro_type ltac:(let step := get_step (ex_coroutine 0) in exact step))
       (fun c0 =>
          nat_rect_nondep
            (fun l => option_branch
                        (fun c : @coro_type nat nat _ _=>
                           r <- resume c $ 1;
                             putN r;
                             Done _ _)
                        (Done _ _)
                        (nth_err _ l i))
            (fun m rec l =>
               pipe (ex_coroutine m : @coro_type nat nat _ _)
                    (fun cm =>
                       rec (cm::l)))
          n [c0]).

Lemma loop_ex'_eq k n :
  loop_ex' k n =
  ltac:(let x := (eval red in (loop_ex' k n)) in
        let x' := coro_to_state x in exact x').
Proof.
  unfold loop_ex'.
  unfold pipe.
  generalize_and_ind.
  - dest_opt.
    repeat (reflexivity || proc_step).
    exfalso. eauto with foldable.
    exfalso. eauto with foldable.
    reflexivity.
  - apply IHk.
    apply GenForall2_cons; simpl in *; eauto with equivc.
Qed.

Inductive tree A := Node : A -> tree A -> tree A -> tree A | Leaf.
Instance tree_Inhabit A : Inhabit (tree A) :=
  { inhabitant := Leaf _ }.

Fixpoint insert A x a0 (t : tree (nat * A)) :=
  match t with
  | Node (y,a) l r =>
    if Nat.leb x y then
      Node (y,a) (insert x a0 l) r
    else
      Node (y,a) l (insert x a0 r)
  | Leaf _ =>
    Node (x,a0) (Leaf _) (Leaf _)
  end.

Fixpoint bsearch A key (t : tree (nat * A)) :=
  match t with
  | Node (x,a) l r =>
    match Nat.compare key x with
    | Eq => Some a
    | Lt => bsearch key l
    | Gt => bsearch key r
    end
  | Leaf _ => None
  end.

Fixpoint replace_map A key a0 (t : tree (nat * A)) :=
  match t with
  | Node (x,a) l r =>
    match Nat.compare key x with
    | Eq => Node (key,a0) l r
    | Lt => Node (x,a) (replace_map key a0 l) r
    | Gt => Node (x,a) l (replace_map key a0 r)
    end
  | Leaf _ => Leaf _
  end.

Fixpoint foldr_map A B (f : A -> B -> B)(init : B)(t : tree (nat * A)) :=
  match t with
  | Node (k,a) l r => foldr_map f (f a (foldr_map f init r)) l
  | Leaf _ => init
  end.
Require Import Arith.
Fixpoint zip_map A1 A2 (m1 : tree (nat * A1))(m2 : tree (nat * A2)) :=
  match m1, m2 with
  | Node (k1,a1) l1 r1, Node (k2,a2) l2 r2 =>
    if Nat.eq_dec k1 k2 then
      match zip_map l1 l2, zip_map r1 r2 with
      | Some ml, Some mr =>
        Some (Node (k1, (a1,a2)) ml mr)
      | _,_ => None
      end
    else
      None
  | Leaf _, Leaf _ => Some (Leaf _)
  | _, _ => None
  end.

Definition from_map_to_list A (t : tree (nat * A)) :=
  foldr_map (fun a accum => a :: accum) [] t.

Lemma fold_right_cons_app : forall A (l l0 : list A),
    fold_right (fun a l' => a::l') l0 l = l ++ l0.
Proof.
  induction l; simpl; intros; congruence.
Qed.

Program Instance map_Foldable : Foldable (fun A => tree (nat * A)) :=
  { foldr := foldr_map;
    zip := zip_map;
    to_list := from_map_to_list
  }.
Next Obligation.
  intros.
  unfold from_map_to_list.
  revert B f b;
  induction x; simpl in *; intros.
  rewrite IHx2.
  destruct a.
  rewrite IHx1.
  rewrite IHx1.
  replace (f a
       (fold_right f b
                   (foldr_map (fun (a0 : A) (accum : list A) => a0 :: accum) [] x2)))
  with (fold_right f b (a :: foldr_map (fun a0 accum => a0 :: accum) [] x2)) by auto.
  rewrite <- fold_right_app.
  f_equal.
  setoid_rewrite IHx1 at 2.
  setoid_rewrite IHx2 at 2.
  replace ((a
     :: fold_right (fun (a0 : A) (accum : list A) => a0 :: accum) []
     (foldr_map (fun (a0 : A) (accum : list A) => a0 :: accum) [] x2)))
  with (fold_right (fun (a0 : A) (accum : list A) => a0 :: accum) []
                   (a ::foldr_map (fun (a0 : A) (accum : list A) => a0 :: accum) [] x2)) by auto.
  rewrite <- fold_right_app.
  rewrite fold_right_cons_app.
  rewrite fold_right_cons_app.
  do 2 rewrite app_nil_r.
  auto.
  auto.
Qed.
Next Obligation.
  unfold from_map_to_list.
  enough (forall l1 l2 l, zip_list l1 l2 = Some l ->
                          Some
    (foldr_map (fun (a : A1 * A2) (accum : list (A1 * A2)) => a :: accum) l x) =
  zip_list (foldr_map (fun (a : A1) (accum : list A1) => a :: accum) l1 x1)
    (foldr_map (fun (a : A2) (accum : list A2) => a :: accum) l2 x2)) by auto.
  revert x x2 H.
  induction x1; simpl in *; intros.
  destruct a.
  destruct x2; simpl in *; [|congruence].
  destruct p.
  destruct (Nat.eq_dec n n0); [|congruence].
  subst.
  destruct (zip_map x1_1 x2_1) eqn:?; simpl in *; [|congruence].
  destruct (zip_map x1_2 x2_2) eqn:?; simpl in *; [|congruence].
  inversion H. subst.
  simpl.
  eapply IHx1_1 in Heqo.
  rewrite <- Heqo.
  reflexivity.
  simpl.
  eapply IHx1_2 in Heqo0.
  rewrite <- Heqo0.
  simpl.
  reflexivity.
  auto.
  destruct x2; [congruence|].
  inversion H. subst.
  auto.
Qed.

Lemma GenForall2_bsearch_Some_None : forall A1 A2 (R : A1 -> A2 -> Prop) m1 m2 k a,
    GenForall2 R m1 m2 ->
    bsearch k m1 = Some a ->
    bsearch k m2 = None ->
    False.
Proof.
  intros.
  destruct H. destruct H.
  clear H2.
  revert x m2 H H1.
  induction m1; intros; simpl in *.
  destruct a0.
  destruct m2.
  destruct p.
  simpl in H1.
  destruct (k ?= n0) eqn:?.
  congruence.
  destruct (Nat.eq_dec n n0); [|congruence].
  subst.
  rewrite Heqc in H0.
  destruct (zip_map m1_1 m2_1) eqn:?; [|congruence].
  eauto.
  destruct (Nat.eq_dec n n0); [|congruence].
  subst.
  rewrite Heqc in H0.
  destruct (zip_map m1_1 m2_1) eqn:?; [|congruence].
  destruct (zip_map m1_2 m2_2) eqn:?; [|congruence].
  eauto.
  congruence.
  congruence.
Qed.

Lemma GenForall2_bsearch_None_Some : forall A1 A2 (R : A1 -> A2 -> Prop) m1 m2 k a,
    GenForall2 R m1 m2 ->
    bsearch k m1 = None ->
    bsearch k m2 = Some a ->
    False.
Proof.
  intros.
  destruct H. destruct H.
  clear H2.
  revert x m2 H H1.
  induction m1; intros; simpl in *.
  destruct a0.
  destruct m2; [|congruence].
  destruct p.
  destruct (Nat.eq_dec n n0); [|congruence].
  subst.
  simpl in H1.
  destruct (k ?= n0) eqn:?.
  congruence.
  destruct (zip_map m1_1 m2_1) eqn:?; [|congruence].
  destruct (zip_map m1_2 m2_2) eqn:?; [|congruence].
  eauto.
  destruct (zip_map m1_1 m2_1) eqn:?; [|congruence].
  destruct (zip_map m1_2 m2_2) eqn:?; [|congruence].
  eauto.
  destruct m2.
  congruence.
  simpl in *.
  congruence.
Qed.
Inductive Forall2_map A1 A2 (R : A1 -> A2 -> Prop) : tree (nat * A1) -> tree (nat * A2) -> Prop :=
| FMLeaf : Forall2_map R (Leaf _) (Leaf _)
| FMNode : forall k a1 a2 l1 l2 r1 r2,
    R a1 a2 -> Forall2_map R l1 l2 -> Forall2_map R r1 r2 ->
    Forall2_map R (Node (k, a1) l1 r1) (Node (k, a2) l2 r2).

Lemma GenForall2_Forall2_map : forall A1 A2 (R : A1 -> A2 -> Prop) m1 m2,
    GenForall2 R m1 m2 <-> Forall2_map R m1 m2.
Proof.
  intros.
  split.
  revert m2.
  induction m1; intros.
  destruct H. destruct H.
  destruct m2; simpl in *.
  destruct a.
  destruct p.
  destruct (Nat.eq_dec n n0); [|congruence].
  subst.
  destruct (zip_map m1_1 m2_1) eqn:?; [|congruence].
  destruct (zip_map m1_2 m2_2) eqn:?; [|congruence].
  inversion H.
  subst.
  simpl in H0.
  econstructor.
  admit.
  apply IHm1_1.
  exists t0.
  split. auto.
  admit.
  apply IHm1_2.
  exists t1.
  split. auto.
  admit.
  destruct a. congruence.
  destruct H. destruct H.
  destruct m2.
  simpl in H. congruence.
  constructor.
  revert m2.
  induction m1; intros.
  inversion H. subst.
  apply IHm1_1 in H5.
  apply IHm1_2 in H6.
  destruct H5. destruct H0.
  destruct H6. destruct H2.
  exists (Node (k,(a1,a2)) x x0).
  split.
  simpl.
  destruct (Nat.eq_dec k k); [|congruence].
  simpl in H0.
  rewrite H0.
  simpl in H2.
  rewrite H2.
  auto.
  simpl.
  admit.
  inversion H.
  subst.
  exists (Leaf _).
  split; simpl; auto.
Admitted.

Lemma GenForall2_bsearch_Some : forall A1 A2 (R : A1 -> A2 -> Prop) m1 m2 k a1 a2,
    GenForall2 R m1 m2 ->
    bsearch k m1 = Some a1 ->
    bsearch k m2 = Some a2 ->
    R a1 a2.
Proof.
  intros.
  apply GenForall2_Forall2_map in H.
  revert m2 a1 a2 H H0 H1.
  induction m1; simpl in *; intros.
  inversion H. subst.
  simpl in H1.
  destruct (k ?= k0) eqn:?.
  inversion H0. subst.
  inversion H1. subst.
  auto.
  eauto.
  eauto.
  congruence.
Qed.

Lemma GenForall2_bsearch_Some_equiv_coro : forall A B (IA : Inhabit A) (IB : Inhabit B) state (step : step_type (const_yield A) (const_yield B) state) x1 x2 n a1 a2,
    GenForall2 (fun (coro : coro_type step) (st : state) => equiv_coro' step st coro) x1 x2 ->
    bsearch n x1 = Some a1 ->
    bsearch n x2 = Some a2 ->
    equiv_coro' step a2 a1.
Proof.
  intros.
  eapply (GenForall2_bsearch_Some (R := fun c s => equiv_coro' step s c)).
  apply H.
  eauto.
  eauto.
Qed.

Hint Resolve GenForall2_bsearch_Some_None GenForall2_bsearch_None_Some GenForall2_bsearch_Some_equiv_coro : foldable.

Definition coro_map_loop fuel :=
  pipe (ex_coroutine 0)
       (fun c : coro_type ltac:(let step := get_step (ex_coroutine 0) in exact step) =>
          nat_rect_nondep
            (fun _ => Done _ _)
            (fun _ rec m' =>
               key <- getN;
                 option_branch
                   (fun c : @coro_type nat nat _ _ =>
                      n <- getN;
                        r <- resume c $ n;
                        putN r;
                        rec (replace_map key c m'))
                   (rec m')
                   (bsearch key m'))
            fuel (Node (0,c) (Leaf _) (Leaf _))).

(*
Lemma coro_map_loop_ex : forall fuel,
    coro_map_loop fuel =
    ltac:(let x := (eval red in (coro_map_loop fuel)) in
          let x' := coro_to_state x in exact x').
Proof.
  intros.
  unfold coro_map_loop.
  unfold pipe.
  generalize_and_ind.
  reflexivity.
  f_equal.
  extensionality key.
  dest_opt.
  f_equal.
  extensionality r.
  proc_step.
  eapply GenForall2_bsearch_Some_equiv_coro.
  eauto.
  eauto.
  apply Heqo0.
  eauto.
  eauto with typeclass_instances.
  rewrite <- Heqo0.
  pattern (bsearch key t1).
  refine eq_refl.
  match goal with
    |- ?lhs = ?rhs =>
    tryif constr_eq lhs rhs then
      idtac
    else
      fail 0
  end.
*)