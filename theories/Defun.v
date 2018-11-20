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
| skipE : forall T, unit -> effect T.


Fixpoint seqt eff a (e1 : t eff unit) (e2 : t eff a) :=
  match e1 with
  | Pure _ _ => e2
  | Eff ef prog => Eff ef (fun x => seqt (prog x) e2)
  end.

Fixpoint foreach eff a T (l : list T)(e : t eff a)(f : T -> t eff a -> t eff a) :=
  match l with
  | [] => e
  | x::l' => f x (foreach l' e f)
  end.

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

Definition step_range (state : Type) :=
  option {ty : Set & (effect ty * (ty -> state))%type }.

Open Scope type_scope.

Inductive equiv (state a : Type)(step : state -> step_range state) :
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
      = Some (existT _ _ (skipE unit tt, f)) ->
      equiv step (f tt) (prog tt) ->
      equiv step current (Eff (skipE unit tt) prog)
| EquivPure :
    forall (current : state)(x : a),
      step current = None ->
      equiv step current (Pure _ x)
| EquivStateSkip :
    forall (current : state)(T : Type)(f : T -> state)(e : t effect a),
      step current
      = Some (existT _ _(skipE T tt, f)) ->
      (forall x:T, equiv step (f x) e) ->
      equiv step current e
| EquivGeneralize :
    forall (current : state)(T : Type)(x0 : T)(f : T -> state)(e' : T -> t effect a) e,
      step current
      = Some (existT _ _ (skipE T tt, f)) ->
      e' x0 = e ->
      (forall x:T, equiv step (f x) (e' x)) ->
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
  | (?x,n) => constr:((x,m))
  | (?x,?k) => let x' := env_subst x n m in
               constr:((x',k))
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
    let f := open_constr:(_  : ty_env -> step_range state) in
    eapply (@EquivStateSkip _ _ (step_f f) (ptr env) _ nextptr)
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
          | _ => open_constr:(fun n:nat => (env,n))
          end
      in
      let step_f := ptr_to_step_f ptr in
      let f := open_constr:(_  : ty_env -> step_range state) in
      let f' := open_constr:(_) in
      eapply (@EquivEffGet _ _ (step_f (f ||| f')) (ptr (inl env))
                           (fun n => ptr (inr (inl (env_f' n)))));
      [unify_fun|
       let n := fresh "n" in
       intro n; derive constr:(env_f' n)]
    | Eff (putE ?n) ?e =>
      let step_f := ptr_to_step_f ptr in
      let f  := open_constr:(_ : ty_env -> step_range state) in
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
      let f := open_constr:(_  : ty_env -> step_range state) in
      let f' := open_constr:(_) in
      let env' := (eval simpl in env) in
      let env0 := env_subst env' m 0 in
      eapply (@EquivStateSkip _ _ (step_f (f ||| f')) (ptr (inl env)) unit
                              (fun _ => match m with
                                        | O =>
                                          ptr (inr (inl (inl env0)))
                                        | S m' =>
                                          ptr (inr (inr (@inl nat _ _)))
                                        end));
      [ unify_fun
      | let m' := fresh "m'" in
        destruct m as [|m'];
        [ derive env0 | let envm' := env_subst env' m m' in derive envm' ]
      ]
    | _ =>
      let p := leftmost prog in
      tryif is_fix p then
        (skip_to env open_constr:(fun _:unit => ptr (inr env));
         intros;
         [unify_fun
         | skip_to env open_constr:(fun _:unit => _);
           intros;
           [unify_fun|progress repeat match goal with H : _ |- _ => refine (H _) end]])
        || (
          let step_f := ptr_to_step_f ptr in
          let f := open_constr:(_  : ty_env -> step_range state) in
          let f' := open_constr:(_) in
          let env' := (eval simpl in env) in
          let m := match prog with _ ?k => k end in
          let env0 := match type of m with
                      | nat => env_subst env' m 0
                      | list ?A => env_subst env' m (@nil A)
                      end
          in
          let k := fresh "k" in
          let rec generalize_args e tac :=
              lazymatch e with
              | ?e' m =>
                lazymatch p with
                | context[m] =>
                  eapply (@EquivGeneralize _ _ (step_f (f ||| f')) (ptr (inl env)) _ m (fun k:nat => match m with
                                                                                                   | O => ptr (inr (inl (inl (env0,k))))
                                                                                                   | S m' => ptr (inr (inr (inl (_, k))))
                                                                                                   end));
                  [ unify_fun
                  | match goal with
                      |- ?e ?x = ?f ?x =>
                      match eval pattern x in f with
                        ?g _ => exact (eq_refl: e x = (fun y => g y x) x)
                      end
                    end
                  | let m' := fresh "n'" in
                  induction m as [|m'];
                  intro k;
                  simpl;
                  [ tac env0 0
                  | tac env' m' ]
                  ]
                | _ =>
                  generalize_args e' tac
                end
              | ?e' ?x =>
                eapply (@EquivGeneralize _ _ (step_f (f ||| f')) (ptr (inl env)) _ x (fun k:nat => match m with
                                                                                                   | O => ptr (inr (inl (inl (env0,k))))
                                                                                                   | S m' => ptr (inr (inr (inl (_, k))))
                                                                                                   end));
                [ unify_fun
                | generalize x;
                  intros;
                  lazymatch goal with
                    |- _ ?x = _ =>
                    pattern_rhs x;
                    try apply eq_refl
                  | _ => idtac
                  end
                | let m' := fresh "n'" in
                  induction m as [|m'];
                  intro k;
                  simpl;
                  [ tac env0 0
                  | tac env' m' ]
                ]
              | _ => idtac
              end
          in
          generalize_args prog ltac:(fun env m' =>
                                       let envm' := env_subst env' m m' in
                                       derive (envm',k))
        )
     else fail 0
    end
  end.


Ltac derive_step env :=
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
          | _ => open_constr:(fun n:nat => (env,n))
          end
      in
      let step_f := ptr_to_step_f ptr in
      let f := open_constr:(_  : ty_env -> step_range state) in
      let f' := open_constr:(_) in
      eapply (@EquivEffGet _ _ (step_f (f ||| f')) (ptr (inl env))
                           (fun n => ptr (inr (inl (env_f' n)))));
      [unify_fun|
       let n := fresh "n" in
       intro n]
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
        [unify_fun|]
      end
    | (match ?m with | O => ?progO | S _ => ?progS end) =>
      let step_f := ptr_to_step_f ptr in
      let f := open_constr:(_  : ty_env -> step_range state) in
      let f' := open_constr:(_) in
      let env' := (eval simpl in env) in
      let env0 := env_subst env' m 0 in
      eapply (@EquivStateSkip _ _ (step_f (f ||| f')) (ptr (inl env)) unit
                              (fun _ => match m with
                                        | O =>
                                          ptr (inr (inl (inl env0)))
                                        | S m' =>
                                          ptr (inr (inr (@inl nat _ _)))
                                        end));
      [ unify_fun
      | let m' := fresh "m'" in
        destruct m as [|m']
      ]
    | _ =>
      let p := leftmost prog in
      tryif is_fix p then
        (skip_to env open_constr:(fun _:unit => ptr (inr env));
         intros;
         [ unify_fun
         | skip_to env open_constr:(fun _:unit => _);
          intros;
          [unify_fun|progress eauto]])
        || (
          let step_f := ptr_to_step_f ptr in
            let f := open_constr:(_  : ty_env -> step_range state) in
            let f' := open_constr:(_) in
            let env' := (eval simpl in env) in
            let m := match prog with _ ?k => k end in
            let env0 := match type of m with
                        | nat => env_subst env' m 0
                        | list ?A => env_subst env' m (@nil A)
                        end
            in
            
          let rec generalize_args e tac :=
              lazymatch e with
              | ?e' m =>
                lazymatch p with
                | context[m] =>
                  eapply (@EquivGeneralize _ _ (step_f (f ||| f')) (ptr (inl env)) _ m (fun k:nat => match m with
                                                                                                   | O => ptr (inr (inl (inl (env0,k))))
                                                                                                   | S m' => ptr (inr (inr (inl (_, k))))
                                                                                                   end));
                  [ unify_fun
                  | match goal with
                      |- ?e ?x = ?f ?x =>
                      match eval pattern x in f with
                        ?g _ => exact (eq_refl: e x = (fun y => g y x) x)
                      end
                    end
                  |
                  ]
                | _ =>
                  generalize_args e' tac
                end
              | ?e' ?x =>
                eapply (@EquivGeneralize _ _ (step_f (f ||| f')) (ptr (inl env)) _ x (fun k:nat => match m with
                                                                                                   | O => ptr (inr (inl (inl (env0,k))))
                                                                                                   | S m' => ptr (inr (inr (inl (_, k))))
                                                                                                   end));
                [ unify_fun
                | generalize x; try reflexivity
                | let m' := fresh "n'" in
                  induction m as [|m'];
                  [ tac env0 0
                  | tac env' m' ]
                ]
              | _ => idtac
              end
          in
          generalize_args prog ltac:(fun env m' =>
                                       let envm' := env_subst env' m m' in
                                       idtac)
        )
     else idtac
    end
  end.

Definition ex : t effect unit :=
  n <- get;
    n0 <- get;
    n1 <- get;
    put (n + n0 + n1);
    Pure _ tt.

Definition ex_derive :
  {state & {step & {init | @equiv state _ step init ex}}}.
Proof.
  unfold ex.
  repeat eexists.
  derive tt.
Defined.

Fixpoint ex3' (a n : nat) : t effect unit :=
  match n with
  | O => put a; Pure _ tt
  | S n' => x <- get; ex3' (x + a) n'
  end.

Definition ex3'_derive :
  {state & {step & forall a n, { init | @equiv state _ step init (ex3' a n) }}}.
Proof.
  unfold ex3'.
  repeat eexists.
  derive (a,n).
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


Definition ex3 : t effect unit :=
  n <- get; ex3' 5 n.

Definition ex3_derive :
  {state & {step & {init | @equiv state _ step init ex3 }}}.
Proof.
  unfold ex3, ex3'.
  repeat eexists.
  derive tt.
Defined.  

Definition ex5 : t effect unit :=
  n <- get;
    (fix f m :=
       match m with
       | O => put n; Pure _ tt
       | S m' => put n; f m'
       end) n.

Definition ex5_derive :
  { state & { step & { init | @equiv state _ step init ex5 }}}.
Proof.
  unfold ex5.
  repeat eexists.
  derive tt.
Defined.

Eval cbv [ex5 ex5_derive sum_merge prod_curry projT1 projT2] in (projT1 (projT2 ex5_derive)).

Definition double_loop : t effect unit :=
  n <- get;
    (fix f m :=
       match m with
       | O => put 0; Pure _ tt
       | S m' =>
         x <- get;
           (fix g k :=
              match k with
              | O => f m'
              | S k' => put 1; g k'
              end) x
       end) n.

Definition double_loop_derive :
  {state & {step & {init | @equiv state _ step init double_loop}}}.
Proof.
  unfold double_loop.
  repeat eexists.
  derive tt.
  derive_step n.
  
Defined.

Definition ex_list : t effect unit :=
  n <- get;
    (fix f l m :=
       match m with
       | O => put 0; Pure _ tt
       | S m' =>
         x <- get;
           (fix g l' :=
              match l' with
              | [] => f (x::l) m'
              | a::rest =>
                put a;
                  g rest
              end) l
       end) [] n.
