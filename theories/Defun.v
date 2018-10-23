Require Import List PeanoNat.
(*Require Import StateMachines.Plugin.*)
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


Lemma equal_f : forall (A B : Type)(f g : A -> B) x,
    f = g -> f x = g x.
  intros.
  congruence.
Qed.

Ltac unify_fun :=
  simpl;
  repeat curry_lhs;
  let rec unify_fun_aux :=
      match goal with
        |- _ ?x = _ =>
        pattern_rhs x;
        apply equal_f;
        apply eq_refl
        || unify_fun_aux
      end
  in
  unify_fun_aux.

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
  | _ => env
  end.

Ltac leftmost c :=
  lazymatch c with
  | ?c' _ => leftmost c'
  | _ => c
  end.

Ltac skip_to env nextptr :=
  lazymatch goal with
    |- @equiv ?state ?a ?step ?current _ =>
    let ptr := open_constr:(?[ptr]) in
    context_of current env ptr;
    let step_f := ptr_to_step_f ptr in
    let ty_env := type of env in
    let f := open_constr:(_  : ty_env -> step_range state a ) in
    eapply (@EquivStateSkip _ _ (step_f f) (ptr env)
                            (fun _ => nextptr))
  end.

Ltac is_concr_nat n :=
  match n with
  | S ?n' => is_concr_nat n'
  | O => idtac
  end.

Ltac derive env :=
  lazymatch goal with
    |- @equiv ?state ?a ?step ?current ?prog =>
    let ptr := open_constr:(?[ptr]) in
    context_of current open_constr:(inl _) ptr;
    let ty_env := type of env in
    lazymatch prog with
    | Eff (getE tt) _ =>
      let env_f' :=
          lazymatch env with
          | tt => open_constr:(fun n:nat => n)
          | _ => open_constr:(fun n:nat => (n,env))
          end
      in
      let step_f := ptr_to_step_f ptr in
      let f := open_constr:(_  : ty_env -> step_range state a ) in
      let f' := open_constr:(_) in
      eapply (@EquivEffGet _ _ (step_f (f ||| f')) (ptr (inl env))
                           (fun n => ptr (inr (inl (env_f' n)))));
      [unify_fun|
       let n := fresh "n" in
       intro n; derive constr:(env_f' n)]
    | Eff (putE ?n) ?e =>
      let step_f := ptr_to_step_f ptr in
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
      let step_f := ptr_to_step_f ptr in
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
    | _ =>
      let p := leftmost prog in
     (* tryif is_fix p then*)
        (  skip_to env open_constr:(ptr (inr env));
          [unify_fun|
           skip_to env open_constr:(_);
           [unify_fun|progress auto]])
        || (
          let step_f := ptr_to_step_f ptr in
            let f := open_constr:(_  : ty_env -> step_range state a ) in
            let f' := open_constr:(_) in
            let env' := (eval simpl in env) in
            let m := match prog with _ ?k => k end in
            let env0 := env_subst env' m 0 in
            eapply (@EquivStateSkip _ _ (step_f (f ||| f')) (ptr (inl env))
                                    (fun _ => match m with
                                              | O =>
                                                ptr (inr (inl (inl env0)))
                                              | S m' =>
                                                ptr (inr (inr _))
                                              end));
            [ unify_fun
            | let rec generalize_args e tac :=
                  lazymatch e with
                  | ?e' m => generalize_args e' tac
                  | ?e' ?x =>
                    tryif is_concr_nat x then
                        let s := fresh "n" in
                        generalize x at 1 as s;
                        generalize_args e'
                                        ltac:(fun env m' =>
                                                intro s;
                                                tac constr:((s,env)) m')
                    else
                      (generalize dependent x;
                       generalize_args e' ltac:(fun env m' =>
                                                  intro x;
                                                  tac env m'))
                  | _ =>
                    let m' := fresh "n'" in
                    induction m as [|m'];
                    [ tac env0 0
                    | tac env m'
                    ]
                  end
              in
              generalize_args prog ltac:(fun env m' =>
                                           let envm' := env_subst env' m m' in
                                           derive envm')
            ]
        )
     (* else idtac*)
    end
  end.

Definition ex : t effect unit :=
  n <- get;
    n0 <- get;
    n1 <- get;
    put (n + n0 + n1);
    Pure _ tt.


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
  n <- get; ex3' 5 n.

Definition ex3'_derive :
  {state & {step & forall a n, { init | @equiv state _ step init (ex3' a n) }}}.
Proof.
  unfold ex3'.
  repeat eexists.

  derive (n,a).
Defined.

Eval cbv in projT1 ex3'_derive.

Eval cbv [ex3'_derive projT1 projT2 sum_merge prod_curry] in
    (projT1 (projT2 ex3'_derive)).

Definition ex3'' : t effect unit :=
  n <- get;
    a <- get;
    ex3' a n.

Definition ex3''_derive :
  {state & {step & {init | @equiv state _ step init ex3''}}}.
Proof.
  unfold ex3'',ex3'.
  repeat eexists.

  derive tt.
Defined.

Set Printing Evars.
Definition ex3_derive :
  {state & {step & {init | @equiv state _ step init ex3 }}}.
Proof.
  unfold ex3, ex3'.
  repeat eexists.

  derive tt.
  simpl.
