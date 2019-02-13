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
  lazymatch env with
  | x__ => true
  | (?env',x__) => true
  | (?env',_) => mem x__ env'
  | _ => false
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

Ltac free_var exp env :=
  lazymatch exp with
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

Ltac step_next enext prog env :=
  lazymatch goal with
  | |- @equiv ?state ?a ?step (apply ?ptr (inl _)) _ =>
    lazymatch type of prog with
      ?ty -> _ =>
      let h := fresh "h" in
      set (h := inhabitat : ty);
      let p := (eval simpl in (prog h)) in
      lazymatch p with
      | Pure _ _ =>
        let e := open_constr:(fun _:ty => ptr (inr tt)) in
        unify enext e
      | Eff ?e ?prog' =>
        let env' := free_var p env in
        let env'' := free_var p h in
        let b := mem h env'' in
        lazymatch b with
        | true =>
          let e := open_constr:(fun h:ty => apply (fun x => ptr (inr x)) (inl (env',h))) in
          unify enext e
        | false =>
          let e := open_constr:(fun _:ty => apply (fun x => ptr (inr x)) (inl env')) in
          unify enext e
        end
      | match ?m with O => _ | S m' => _ end =>
        lazymatch m with
        | h =>
          let e := open_constr:(fun k:ty => match k return state with O => apply (fun x => ptr (inr (inl x))) _ | S k' => apply (fun x => ptr (inr (inr x))) _ end) in
          unify enext e
        | _ =>
          let e := open_constr:(match m return ty -> state with O => _ | S m' => _ m' end) in
          unify enext e
        end
      end
    end
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

Ltac fill_step :=
  lazymatch goal with
  | |- @equiv ?state ?a ?step ?init ?p =>
    lazymatch p with
    | Pure _ _ =>
      eapply EquivPure;
      unfold sum_merge; rewrite apply_def;
      unify_fun
    | Eff ?e ?prog =>
      lazymatch init with
      | apply ?ptr (inl ?env) =>
        let r := (eval simpl in (step (ptr (inl env)))) in
        lazymatch r with
        | ?f (inl _) =>
          let splitted := open_constr:(_ ||| _) in
          unify f splitted
        | _ => idtac
        end;
        let enext := open_constr:(_) in
        step_next enext prog env;
        eapply (EquivEff _ (next := enext));
        [ unfold sum_merge; rewrite apply_def; simpl; unify_fun | intros]
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
  let e := open_constr:(apply (fun x => x) (inl tt)) in
  unify ?init e.
  fill_step.
  fill_step.
  fill_step.
  fill_step.
Defined.

Eval cbv [ex1_derive ex1 sum_merge projT2 projT1] in (projT1 ex1_derive).


(*
Goal {state & {step & {init | @equiv state _ step init
                                     (n <- get;
                                        match n with
                                        | O => put 0; Pure _ tt
                                        | S n' => put n'; Pure _ tt
                                        end)}}}.
Proof.
  do 2 eexists.
  eexists ?[init].
  let e := open_constr:(apply (fun x => x) (inl tt)) in
  unify ?init e.
  fill_step.
  destruct x.
  fill_step.
*)
