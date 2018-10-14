Require Import List PeanoNat.
Require Import StateMachines.Plugin.
Import ListNotations.
Set Universe Polymorphism.

Set Implicit Arguments.

Definition sum_merge (A B C : Type)(f : A -> C)(g : B -> C)(x : sum A B) :=
  match x with
  | inl a => f a
  | inr b => g b
  end.

Infix "|||" := sum_merge (at level 60).

Inductive t (eff : Type -> Type) (a : Type) :=
| Pure : a -> t eff a
| Eff : forall T, eff T -> (T -> t eff a) -> t eff a.

Inductive effect : Type -> Type :=
| getE : unit -> effect nat
| putE : nat -> effect unit
| skipE : unit -> effect unit.


Notation "n <- 'get' ; e" := (Eff (getE tt) (fun n => e)) (at level 100, right associativity).
Notation "'put' n ; e" := (Eff (putE n) (fun _ => e)) (at level 100).
Notation "'skip' ; e" := (Eff (skipE tt) (fun _ => e)) (at level 100).

(*
n <- get;
put (1 + n);
 *)

Definition ex1 : t effect unit:=
  n <- get;
    put (1 + n);
    Pure _ tt.

Definition step_range (state a : Type) :=
  option {ty : Set & (effect ty * (ty -> state))%type }.

Open Scope type_scope.

Inductive equiv (state a : Type)(step : state -> step_range state a) :
  state -> t effect a -> Prop :=
| EquivEffGet :
    forall (current : state)(f : nat -> state)(prog : nat -> t effect a),
      step current
      = Some (existT _ _ (getE tt, f)) ->
      (forall n : nat, equiv step (f n) (prog n)) ->
      equiv step current (Eff (getE tt) prog)
| EquivEffPut :
    forall (current : state)(f : unit -> state)(prog : unit -> t effect a) n,
      step current
      = Some (existT _ _ (putE n, f)) ->
      equiv step (f tt) (prog tt) ->
      equiv step current (Eff (putE n) prog)
| EquivEffSkip :
    forall (current : state)(f : unit -> state)(prog : unit -> t effect a),
      step current
      = Some (existT _ _ (skipE tt, f)) ->
      equiv step (f tt) (prog tt) ->
      equiv step current (Eff (skipE tt) prog)
| EquivPure :
    forall (current : state)(x : a),
      step current = None ->
      equiv step current (Pure _ x)
| EquivStateSkip :
    forall (current : state)(f : unit -> state)(e : t effect a),
      step current
      = Some (existT _ _(skipE tt, f)) ->
      equiv step (f tt) e ->
      equiv step current e.


Ltac context_of_aux t1 t2 ctx result :=
  match t1 with
  | ?f ?t1' => context_of_aux t1' t2 open_constr:(fun x => ctx (f x)) result
  | _ => unify t1 t2;
         unify result ctx
  end.

Ltac context_of t1 t2 result :=
  context_of_aux t1 t2 open_constr:(fun x => x) result.

Ltac get_match env ptr env_f step_f :=
  match goal with
    |- @equiv ?state ?a ?step ?current
              (Eff (getE tt)
                   (fun n => match ?m with
                             | O => ?progO
                             | S m' => ?progS
                             end)) =>
    let ty_env := type of env in
    eapply (@EquivEffGet _ _
                         ((fun _ =>
                            Some (existT _ _
                                         (getE tt,
                                          step_f (fun n:nat =>
                                            match n with
                                            | O => ptr (inr (inl (inl env)))
                                            | S n' => ptr (inr (inr (inl (env_f n'))))
                                            end)))) ||| _)
                         (ptr (inl env)));
    [simpl; apply eq_refl|]
  end.

Ltac ptr_to_step_f_aux ptr accum :=
  let ty := match type of ptr with
              ?Ty -> _ => Ty
            end
  in
  lazymatch eval simpl in ptr with
  | (fun x:ty => inl ?ptr') =>
    let g := open_constr:(_) in
    ptr_to_step_f_aux (fun x:ty => ptr') open_constr:(fun f => accum (f ||| g))
  | (fun x:ty => inr ?ptr') =>
    let g := open_constr:(_) in
    ptr_to_step_f_aux (fun x:ty => ptr') open_constr:(fun f => accum (g ||| f))
  | inl =>
    let g := open_constr:(_) in
    open_constr:(fun f => accum (f ||| g))
  | inr =>
    let g := open_constr:(_) in
    open_constr:(fun f => accum (g ||| f))
  | _ =>
    accum
  end.

Ltac ptr_to_step_f ptr :=
  ptr_to_step_f_aux ptr open_constr:(fun f => f).


Ltac curry_lhs :=
  match goal with
    |- ?f (_,_) = _ =>
    let f' := open_constr:(prod_curry _) in
    unify f f'; unfold prod_curry
  end.



Ltac pattern_rhs term :=
  match goal with
    |- _ = ?X =>
    let x := fresh "x" in
    set (x := X); pattern term in x; subst x
  end.

Ltac unify_fun :=
  simpl;
  repeat curry_lhs;
  match goal with
    |- _ ?x = _ => pattern_rhs x; apply eq_refl
  end.

Ltac unify_to_subterm_im t1 t2 :=
  match t1 with
  | _ ?t1' => unify_to_subterm_im t1' t2
  | _ => unify t1 t2
  end.

Ltac env_subst env n m :=
  lazymatch env with
  | n => m
  | (n,?x) => constr:((m,x))
  | (?k,?x) => let x' := env_subst x n m in
               constr:((k,x'))
  | _ => constr:((m,env))
  end.

Ltac leftmost c :=
  lazymatch c with
  | ?c' _ => leftmost c'
  | _ => c
  end.


Ltac derive env :=
  lazymatch goal with
    |- @equiv ?state ?a ?step ?current ?prog =>
    let ptr := open_constr:(?[ptr]) in
    context_of current open_constr:(inl _) ptr;
    let step_f := ptr_to_step_f ptr in
    let ty_env := type of env in
    lazymatch prog with
    | Eff (getE tt) _ =>
      let env_f' :=
          lazymatch env with
          | tt => open_constr:(fun n:nat => n)
          | _ => open_constr:(fun n:nat => (n,env))
          end
      in
      let f := open_constr:(_  : ty_env -> step_range state a ) in
      let f' := open_constr:(_) in
      eapply (@EquivEffGet _ _ (step_f (f ||| f')) (ptr (inl env))
                           (fun n => ptr (inr (inl (env_f' n)))));
      [unify_fun|
       let n := fresh "n" in
       intro n; derive constr:(env_f' n)]
    | Eff (putE ?n) ?e =>
      let f  := open_constr:(_ : ty_env -> step_range state a) in
      lazymatch e with
      | (fun _ => Pure _ _) =>
        eapply (@EquivEffPut _ _ (step_f (f ||| (fun _ => None))) (ptr (inl env))
                             (fun _ => ptr (inr env)));
        [try unify_fun|eapply EquivPure; auto]
      | _ =>
        let f' := open_constr:(_) in
        eapply (@EquivEffPut _ _ (step_f (f ||| f')) (ptr (inl env))
                             (fun _ => ptr (inr (inl env))));
        [unify_fun|derive env]
      end
    | (match ?m with | O => ?progO | S _ => ?progS end) =>
      let f := open_constr:(_  : ty_env -> step_range state a ) in
      let f' := open_constr:(_) in
      let env' := (eval simpl in env) in
      let env0 := env_subst env' m 0 in
      eapply (@EquivStateSkip _ _ (step_f (f ||| f')) (ptr (inl env))
                              (fun _ => match m with
                                        | O =>
                                          ptr (inr (inl (inl env0)))
                                        | S m' =>
                                          ptr (inr (inr (@inl nat _ _)))
                                        end));
      [ unify_fun
      | let m' := fresh "m'" in
        destruct m as [|m'];
        [ derive env0 | let envm' := env_subst env' m m' in derive envm' ]]
    | _ => idtac
    end
  end.

Ltac induct env m :=
  lazymatch goal with
    |- @equiv ?state ?a ?step ?current ?prog =>
    let ptr := open_constr:(?[ptr]) in
    context_of current open_constr:(inl _) ptr;
    let step_f := ptr_to_step_f ptr in
    let ty_env := type of env in
    let f := open_constr:(_  : ty_env -> step_range state a ) in
    let f' := open_constr:(_) in
    let env' := (eval simpl in env) in
    let env0 := env_subst env' m 0 in
    eapply (@EquivStateSkip _ _ (step_f (f ||| f')) (ptr (inl env))
                            (fun _ => match m with
                                      | O =>
                                        ptr (inr (inl (inl env0)))
                                      | S m' =>
                                        ptr (inr (inr (inl _)))
                                      end));
    [ unify_fun
    |
    ]
  end.


Ltac refer env nextptr :=
  lazymatch goal with
    |- @equiv ?state ?a ?step ?current ?prog =>
    let ptr := open_constr:(?[ptr]) in
    context_of current env ptr;
    let step_f := ptr_to_step_f ptr in
    let ty_env := type of env in
    let f := open_constr:(_  : ty_env -> step_range state a ) in
    eapply (@EquivStateSkip _ _ (step_f f) (ptr env)
                            (fun _ => nextptr))
  end.

Definition ex : t effect unit :=
  n <- get;
    n0 <- get;
    n1 <- get;
    put (n + n0 + n1);
    Pure _ tt.

Goal {state & {init & {step | @equiv state _ step init ex }}}.
  unfold ex.
  repeat eexists.
  derive tt.
Defined.

Definition ex4 :=
  n <- get;
    match n with
    | O => put 0; put 1; Pure _ tt
    | S n' => m <- get; put m; Pure _ tt
    end.

Goal {state & {init & {step | @equiv state _ step init ex4}}}.
  unfold ex4.
  repeat eexists.
  derive tt.
Defined.

Goal {state & {init & { step | @equiv state _ step init ex1 }}}.
  unfold ex1.
  repeat eexists.
  derive tt.
Defined.

Definition ex2 : t effect unit :=
  n <- get;
    m <- get;
    put (n + m);
    Pure _ tt.

Goal {state & {init & { step | @equiv state _ step init ex2 }}}.
Proof.
  unfold ex2.
  repeat eexists.
  derive tt.
Defined.


(*
n <- get;
a = 0;
for 0..(n-1)
  x <- get;
  a = a + x;
put a;
 *)

Fixpoint ex3' (a n : nat) : t effect unit :=
  match n with
  | O => put a; Pure _ tt
  | S n' => x <- get; ex3' (x + a) n'
  end.

Definition ex3 : t effect unit :=
  n <- get; ex3' 0 n.

Lemma equal_f : forall (A B : Type)(f g : A -> B) x,
    f = g -> f x = g x.
  intros.
  congruence.
Qed.

Goal {state & {step & forall n a, { init | @equiv state _ step init (ex3' a n) }}}.
Proof.
  unfold ex3'.
  do 2 eexists.
  intros.
  eexists.
  induct (n,a) n.
  revert a.
  induction n; intros.
  - derive (0,a).
    unfold prod_curry. simpl.
    curry_lhs. pattern_rhs a.
    apply equal_f.
    pattern_rhs 0.
    apply eq_refl.
  - (* Show Existentials. *)
    instantiate (1 := (m',a)).
    derive (n,a).
    refer (n0,(n,a))
          open_constr:
    (match n with
     | O => inr (inl (inl (0,Nat.add n0 a)))
     | S n' => inr (inr (inl (n',Nat.add n0 a)))
    end).
    unify_fun.
    apply (IHn (Nat.add n0 a)).
    Grab Existential Variables.
    all:try exact (fun _:unit => tt).
    exact (fun _:unit => None).
    exact unit.
Defined.
