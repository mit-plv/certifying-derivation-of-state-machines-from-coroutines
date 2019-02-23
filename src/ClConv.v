Require Import List PeanoNat Program.Basics FunctionalExtensionality.
Import ListNotations.
Set Universe Polymorphism.

Set Implicit Arguments.

Class habitable (A : Type) :=
  { inhabitat : A }.

Instance nat_habitable : habitable nat :=
  { inhabitat := 0 }.

Instance list_habitable (A : Type) : habitable (list A) :=
  { inhabitat := @nil A }.

Instance unit_habitable : habitable unit :=
  { inhabitat := tt }.

Opaque inhabitat.

Definition sum_merge (A B C : Type)(f : A -> C)(g : B -> C)(x : sum A B) :=
  match x with
  | inl a => f a
  | inr b => g b
  end.

Lemma apply_def : forall A B (f : A -> B)(x : A),
    apply f x = f x.
Proof.
  auto.
Qed.

Opaque apply.

Infix "|||" := sum_merge (at level 60).

Inductive t (eff : Type -> Type) (a : Type) :=
| Pure : a -> t eff a
| Eff : forall T, eff T -> (T -> t eff a) -> t eff a.

Inductive effect : Type -> Type :=
| getE : unit -> effect nat
| putE : nat -> effect unit.

Notation "n <- 'get' ; e" := (Eff (getE tt) (fun n => e)) (at level 100, right associativity).
Notation "'put' n ; e" := (Eff (putE n) (fun _ => e)) (at level 100).


Definition step_range (state : Type) :=
  option {ty : Type & (effect ty * (ty -> state))%type }.

Open Scope type_scope.

Inductive equiv (state a : Type)(step : state -> step_range state) :
  state -> t effect a -> Prop :=
| EquivEff :
    forall (current : state)(T : Type)(next : T -> state)
           (prog : T -> t effect a)(e : effect T),
      step current = Some (existT _ _ (e, next)) ->
      (forall x : T, equiv step (next x) (prog x)) ->
      equiv step current (Eff e prog)
| EquivPure :
    forall (current : state)(x : a),
      step current = None ->
      equiv step current (Pure _ x).

Ltac mem x__ env :=
  lazymatch x__ with
  | O => false
  | tt => false
  | _ =>
    lazymatch env with
    | x__ => true
    | (?env',x__) => true
    | (?env',_) => mem x__ env'
    | _ => false
    end
  end.

Class reify_cls (A : Type)(x : A) := do_reify : A.

Global Hint Extern 0 (@reify_cls _ _)
=> (intros;
      lazymatch goal with
      | [ |- @reify_cls _ ?x ]
        => exact x
end) : typeclass_instances.

Ltac merge t1 t2 :=
  lazymatch t2 with
  | (?t2',?x) =>
    let t := merge t1 t2' in
    let b := mem x t1 in
    lazymatch b with
    | true => constr:(t)
    | false => constr:((t,x))
    end
  | tt => constr:(t1)
  end.

Definition Fix (A:Type)(t:A) := t.

Ltac free_var exp env :=
  lazymatch exp with
  | Fix ?f =>
    lazymatch type of f with
    | nat -> _ =>
      let eO := (eval simpl in (f O)) in
      let vO := free_var eO env in
      let eS := (eval simpl in (f (S inhabitat))) in
      let vS := free_var eS env in
      let v := merge vO vS in
      constr:(v)
    end
  | ?f ?x =>
    let v1 := free_var f env in
    let v2 := free_var x env in
    let v := merge v1 v2 in
    constr:(v)
  | (fun x => _) =>
    let exp' := (eval simpl in (exp inhabitat)) in
    let v := free_var exp' env in
    constr:(v)
  | (match ?m with O => ?e1 | S m' => ?e2 end) =>
    lazymatch constr:(_ : forall m':nat, @reify_cls _ e2) with
    | ?e =>
      let v1 := free_var e1 env in
      let exp' := (eval simpl in (e inhabitat)) in
      let v2 := free_var exp' env in
      let v := merge v1 v2 in
      let b := mem m env in
      lazymatch b with
      | true =>
        let r := merge v constr:((v,m)) in
        r
      | false => constr:(v)
      end
    end
  | _ =>
    let b := mem exp env in
    lazymatch b with
    | true => constr:((tt,exp))
    | false => constr:(tt)
    end
  end.

Ltac remove a t :=
  lazymatch t with
  | (?t',a) => t'
  | (?t',?x) =>
    let v := remove a t' in
    constr:((v,x))
  end.

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
        pattern_rhs x;
        apply equal_f;
        apply eq_refl
        || unify_fun_aux
      end
  in
  unify_fun_aux.

Ltac dest_sum :=
  match goal with
  | |- ?g (@inl ?A ?B _) = ?t =>
    let T := type of t in
    let e := open_constr:((_|||_): A + B -> T) in
    unify g e
  | |- ?g (inr _) = _ =>
    let ty := type of g in
    let e := open_constr:((_|||_): ty) in
    unify g e
  end.

Ltac dest_step :=
  repeat match goal with
           |- context[apply ?f _] => rewrite (apply_def f)
         end;
  simpl;
  repeat (dest_sum; simpl);
  unify_fun.


Ltac next_ptr state :=
  lazymatch state with
  | ?A + (?B + ?T) =>
    let f := next_ptr T in
    open_constr:(fun x => @inr A _ (@inr B _ (f x)))
  | ?A + ?B => open_constr:(fun x => @inr A B x)
  | ?A => open_constr:(fun x:A => x)
  end.

Ltac derive' env :=
  lazymatch goal with
  | |- @equiv ?state ?a ?step ?current ?p =>
    lazymatch p with
    | Pure _ _ =>
      lazymatch current with
      | apply _ _ => idtac
      | ?f _ =>
        let ptr := next_ptr state in
        let e := open_constr:(fun _ => ptr (inl tt)) in
        unify f e;
        eapply EquivPure;
        dest_step
      end
    | Eff ?e ?prog =>
      lazymatch current with
      | inl _ =>
        eapply EquivEff;
        [ dest_step | intros; derive' env ]
      | ?f ?prev =>
        let ptr := next_ptr state in
        let env' := free_var p (env,prev) in
        let b := mem prev env' in
        let ty := type of prev in
        lazymatch b with
        | true =>
          let e := open_constr:(fun x:ty => ptr (inl (env,x))) in
          let e' := (eval simpl in e) in
          unify f e';
          eapply EquivEff;
          [ dest_step
          | intros;
            derive' env]
        | false =>
          let e := open_constr:(fun _:ty => ptr (inl env)) in
          let e' := (eval simpl in e) in
          unify f e';
          eapply EquivEff;
          [ dest_step
          | intros; derive' env ]
        end
      end
    | match ?m with O => _ | S m' => _ end =>
      lazymatch current with
      | ?f ?prev =>
        let x' := fresh in
        let ty := type of prev in
        let e :=
            lazymatch prev with
            | m => open_constr:(fun x => match x return state with O => _ O | S x' => _ x' end)
            | _ => open_constr:(match m return ty -> state with O => _ | S m' => _ end)
            end
        in
        unify f e;
        destruct m
      end
    | ?fn ?m =>
      lazymatch current with
      | ?f ?prev =>
        lazymatch fn with
        | Fix ?fx =>
          let ty := type of prev in
          let x' := fresh "x" in
          let e :=
              lazymatch prev with
              | m => open_constr:(fun x => match x return state with O => _ x | S x' => _ x end)
              | _ => open_constr:(match m return ty -> state with O => _ | S m' => _ end)
              end
          in
          unify f e;
          simpl;
          let tmp := fresh in
          let m' := fresh in
          set (tmp := fn);
          generalize m at 1 6 as m';
          subst tmp;
          unfold Fix;
          induction m'
        | _ => 
          let e := open_constr:(fun _ => _) in
          unify f e;
          simpl;
          eauto
        end
      end
    end
  end.

Definition ex1 : t effect unit:=
  n <- get;
    put n;
    put 1;
    Pure _ tt.

Theorem ex1_derive : {state & {step & {init | @equiv state _ step init ex1}}}.
Proof.
  do 2 eexists.
  eexists ?[init].
  unfold ex1.
  let e := open_constr:(inl tt) in
  unify ?init e.
  derive' tt.
  Grab Existential Variables.
  all: exact unit || exact (fun _ => None).
Defined.

Eval cbv [ex1_derive ex1 sum_merge projT2 projT1] in projT1 (projT2 ex1_derive).


Goal {state & {step & {init | @equiv state _ step init
                                     (n <- get;
                                        m <- get;
                                        match n with
                                        | O => put 0; Pure _ tt
                                        | S n' => put n'; Pure _ tt
                                        end)}}}.
Proof.
  do 2 eexists.
  eexists ?[init].
  let e := open_constr:(inl tt) in
  unify ?init e.
  derive' tt.
  derive' tt.
  derive' (tt,x).
  Grab Existential Variables.
  all: exact unit || exact (fun _ => None).
Defined.

Theorem ex3: {state & {step & {init | @equiv state _ step init
                                     (n <- get;
                                        Fix (fix f y :=
                                           match y with
                                           | O => put n; Pure _ tt
                                           | S y' => put y; f y'
                                           end) n)}}}.
Proof.
  do 2 eexists.
  eexists ?[init].
  let e := open_constr:(inl tt) in
  unify ?init e.
  derive' tt.
  derive' (tt,x).
  derive' (tt,H0,x).
  Grab Existential Variables.
  all: exact unit || exact (fun _ => None).
Defined.

Eval cbv [ex3 sum_merge projT2 projT1] in projT1 (projT2 ex3).
