Require String Vector.
Require Import List FunctionalExtensionality.
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

Definition seqE' A state (x : option (state * option { e : yield_effect & A })) (f : state -> A -> t args_effect rets_effect)(f0 : t args_effect rets_effect) :=
  match x with
  | Some (s, Some (existT _ _ v)) => f s v
  | _ => f0
  end.

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
           seqE' (steps k (nth_fp ss k) yield x) (fun s' v => g v (replace_fp ss k s')) (Done _ _))
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
           seqE' (step init yield x) (fun s' v => g v (FPCons s' ss)) (Done _ _)).

  
  
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
            equiv_parent steps
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
          let f' := open_constr:(prod_curry_rev (fun x => _)) in
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
    nth_fp (replace_fp fp k c) k = c.
Proof.
  intros.
  revert fp.
  induction k; intros.
  revert c fp.
  apply (Vector.caseS' types); intros.
  apply (caseS'_fp fp).
  intros.
  simpl.
  auto.
  revert c fp.
  apply (Vector.caseS' types); intros.
  apply (caseS'_fp fp).
  intros.
  simpl.
  auto.
Qed.

Lemma nth_replace_fp_other : forall n (types: Vector.t Type n) (fp: fin_prod types) k k0 c,
    k <> k0 ->
    nth_fp (replace_fp fp k c) k0 = nth_fp fp k0.
Proof.
  intros n types fp k k0.
  revert types fp.
  apply (Fin.rect2 (fun n k k0 =>
                      forall types fp (c : Vector.nth types k),
                        k <> k0 -> nth_fp (replace_fp fp k c) k0 = nth_fp fp k0)).
  congruence.
  intros n0 f types.
  apply (Vector.caseS' types); intros.
  apply (caseS'_fp fp); intros.
  auto.
  intros n0 f types.
  apply (Vector.caseS' types); intros.
  apply (caseS'_fp fp); intros.
  auto.
  intros n0 f g H types.
  apply (Vector.caseS' types); intros.
  apply (caseS'_fp fp); intros.
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
    |- _ _ _ = ?f _ ?ccs =>
    vec_replace ccs;
    let u := open_constr:(fun v ccs0 => _) in
    unify f u;
    apply eq_refl
  end.

Ltac derive_parent_core :=
  lazymatch goal with
  | |- _ (?g _) =>
    let u := open_constr:(fun v0 => _) in
    unify g u
  | |- _ (fun ss => ?x ss _) =>
    let u := open_constr:(fun ss r => _) in
    unify x u
  | _ => idtac
  end;
  simpl;
  econstructor.

Ltac derive_parent_fix :=
  lazymatch goal with
    |- _ (fun ss => Fix _ ?N) (?g _) =>
    unfold Fix;
    pattern g;
      match goal with
        |- ?G _ =>
        let e := fresh in
        unshelve (evar (e : {h | G h});
                  eassert (E := e : {h | G h}));
          [|
           simpl;
           let e0 := fresh in
           pose (proj2_sig e) as e0;
           unfold e in e0;
           simpl in e0;
           apply e0
          ]
      end;
      induction N; eexists; simpl
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
  derive_parent_core
  || (simpl; derive_parent_fix)
  || prog_eq
  || (
    simpl;
    lazymatch goal with
      |- _ (fun ss => ?X ss _) =>
      let u := open_constr:(fun ss r0 => _) in
      unify X u
    end;
    repeat lazymatch goal with
           | H : {h | _} |- _ => apply (proj2_sig H)
           end).

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


Definition ex_coroutine n : t (fun _:yield_effect => nat) (fun _:yield_effect => nat):=
  m <- yield (S n);
    _ <- yield (n + m)%nat;
    Done _ _.

Definition ex N :=
  let c1 := ex_coroutine in
  let c2 := ex_coroutine in
  n1 <- resume c1 $ 1;
    n2 <- resume c2 $ 2;
    nat_rect _ (fun _ _ => Done args_effect rets_effect)
             (fun N' rec c1 c2 =>
                m1 <- resume c1 $ n1;
                  putN m1;
                  m2 <- resume c2 $ n2;
                  putN m2;
                  rec c1 c2) N c1 c2.

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
  solve_child.
  intros.
  prog_eq.
  intros.
  econstructor.
  solve_child.
  intros.
  prog_eq.
  intros.
  lazymatch goal with
    |- _ (?g _) =>
    let u := open_constr:(fun v0 => _) in
    unify g u
  end.
  cbv beta.
  lazymatch goal with
    |- _ ?g =>
    pattern N, g
  end.
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
  end.
  eapply (nat_rect_sig _ _).
  simpl.
  econstructor.
  intros.
  eexists.
  simpl.
  intros.
  derive_parent_core.
  intros.
  prog_eq.
  intros.
  derive_parent_core.
  intros.
  derive_parent_core.
  intros.
  prog_eq.
  intros.
  derive_parent_core.
  intros.
  lazymatch goal with
    |- _ (fun ss => ?X ss _) =>
    let u := open_constr:(fun ss r0 => _) in
    unify X u
  end.
  cbv beta.
  apply H.
Defined.
Eval simpl in (fun N => proj1_sig (ex_derive_parent N)).

Transparent seqE.

Lemma equiv_parent_eq_general : forall A B n states steps f g,
    @equiv_parent A B n states steps f g ->
    forall cs ss,
      (forall k x next op,
          steps k (nth_fp ss k) yield x = Some (next, op) ->
          equiv' (steps k) next (Vector.nth cs k x) op) ->
      (forall k x,
          steps k (nth_fp ss k) yield x = None ->
          Vector.nth cs k x = Done _ _) ->
      f cs = g ss.
Proof.
  intros A B n states steps f g H.
  induction H; intros; simpl.
  auto.
  f_equal.
  extensionality r.
  auto.
  destruct (steps k (nth_fp ss k) yield x) eqn:?.
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

Definition dummy (A:Type)(x:A) := True.

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

Theorem ex_correct : forall N,
    ex N = proj1_sig (ex_derive_parent N) FPNil.
Proof.
  intros.
  set (x := fun _ => ex N).
  replace (ex N) with (x (Vector.nil _)); subst x.
  erewrite equiv_parent_eq.
  2: apply (proj2_sig (ex_derive_parent N)).
  reflexivity.
  auto.
Qed.

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
        end
      end;
      apply equal_f_dep;
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

Ltac derive env :=
  let N := fresh in
  eexists;
  eexists;
  intro N;
  eexists ?[init];
  lazymatch goal with
    |- equiv _ _ ?p =>
    let tmp := fresh in
    eset (tmp := fun _: Vector.t _ 0 => p);
      replace p with (tmp (Vector.nil _)) by (unfold tmp; auto);
      subst tmp;
      erewrite equiv_parent_eq by (apply (proj2_sig (ex_derive_parent N)))
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

Theorem ex_derive :
  {state & {step & forall N, {init | @equiv _ _ _ state step init (ex N)}}}.
Proof.
  unshelve derive tt;
    exact unit || exact FPNil.
Defined.

Eval cbv [prod_curry sum_merge ex_derive projT1 projT2] in projT1 (projT2 ex_derive).