Require Import List PeanoNat Program.Basics FunctionalExtensionality.
Require Import StateMachines.Plugin.
Import ListNotations.
Set Universe Polymorphism.

Set Implicit Arguments.

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

Inductive aux_effect : Type -> Type :=
| bindE : forall T, T -> aux_effect T
| skipE : unit -> aux_effect unit.


Notation "n <- 'get' ; e" := (Eff (getE tt) (fun n => e)) (at level 100, right associativity).
Notation "'put' n ; e" := (Eff (putE n) (fun _ => e)) (at level 100).

(*
n <- get;
put (1 + n);
 *)

Definition ex1 : t effect unit:=
  n <- get;
    put (1 + n);
    Pure _ tt.

Definition step_range (state : Type) :=
  option {ty : Type & ((effect ty + aux_effect ty) * (ty -> state))%type }.

Open Scope type_scope.

Inductive equiv (state a : Type)(step : state -> step_range state) :
  state -> t effect a -> Prop :=
| EquivEff :
    forall (current : state)(T : Type)(f : T -> state)(prog : T -> t effect a)(e : effect T),
      step current
      = Some (existT _ _ (inl e, f)) ->
      (forall x : T, equiv step (f x) (prog x)) ->
      equiv step current (Eff e prog)
| EquivStateSkip :
    forall (next : state)(current : state)(prog : t effect a),
      step current
      = Some (existT _ _ (inr (skipE tt), (fun _:unit => next))) ->
      equiv step next prog ->
      equiv step current prog
| EquivBind :
    forall(T : Type)(x0 : T)(f : T -> state)(current : state) prog ,
      step current
      = Some (existT _ _ (inr (bindE x0), f)) ->
      equiv step (f x0) prog ->
      equiv step current prog
| EquivPure :
    forall (current : state)(x : a),
      step current = None ->
      equiv step current (Pure _ x).


Lemma get_derive :
  forall state a step A ty_env (ptr : ty_env + (ty_env * nat + A) -> state)
         (env : ty_env) (prog : nat -> t effect a),
    step (apply ptr (inl env))
    = Some (existT _ _ (inl (getE tt),
                        fun n => apply (fun x => ptr (inr x)) (inl (env,n)))) ->
    (forall n, equiv step (apply (fun x => ptr (inr x)) (inl (env,n))) (prog n)) ->
    equiv step (apply ptr (inl env)) (n <- get; prog n).
Proof.
  intros.
  eapply EquivEff; eauto.
Qed.

Lemma put_derive :
  forall state a step A ty_env (ptr : ty_env + (ty_env + A) -> state)
         (env : ty_env) (prog : t effect a) n,
    step (apply ptr (inl env))
    = Some (existT _ _ (inl (putE n),
                        fun _ => apply (fun x => ptr (inr x)) (inl env))) ->
    equiv step (apply (fun x => ptr (inr x)) (inl env)) prog ->
    equiv step (apply ptr (inl env)) (put n; prog).
Proof.
  intros.
  eapply EquivEff; eauto.
Qed.

Lemma EquivGeneralize : forall state a (step : state -> step_range state)(T : Type)(x0 : T)(f : T -> state)(prog' : T -> t effect a) prog (current : state),
    step current
    = Some (existT _ _ (inr (bindE x0), f)) ->
    prog' x0 = prog ->
    (forall x : T, equiv step (f x) (prog' x)) ->
    equiv step current prog.
Proof.
  intros.
  eapply EquivBind.
  apply H.
  rewrite <- H0.
  apply H1.
Qed.


(*
Section ReadL.
  Variable f : list nat -> t effect unit.
  
  Fixpoint readL n accum :=
    match n with
    | O => f accum
    | S n' =>
      x <- get;
        readL n' (accum ++ [x])
    end.
*)
Fixpoint readL (f : list nat -> t effect unit) accum n :=
  match n with
  | O => f accum
  | S n' =>
    x <- get;
      readL f (accum ++ [x]) n'
  end.

Fixpoint printL (e : t effect unit) l :=
  match l with
  | [] => e
  | x::l' =>
    put x;
      printL e l'
  end.

Notation "l <- 'read' n ; e" := (readL (fun l => e) [] n) (at level 100, right associativity).
Notation "'print' l ; e" := (printL e l) (at level 100, right associativity).

Lemma read_derive :
  forall state step A ty_env
         (ptr : ty_env + ((ty_env * nat * list nat) + ((ty_env * list nat) + A)) -> state)
         l0 n e env,
    (forall (l :list nat) m,
        step (apply (fun x => ptr (inr x)) (inl (env, m, l)))
        = Some (existT _ _
                       (inl (getE tt),
                        fun x =>
                          match m with
                          | O => apply (fun x => ptr (inr (inr x)))
                                       (inl (env, l++[x]))
                          | S m' =>
                            apply (fun x => ptr (inr x))
                                  (inl (env, m', l++[x]))
                          end))) ->
    step (apply ptr (inl env))
    = Some (existT _ _
                   (inr (bindE n),
                    fun m =>
                      match m with
                      | O => apply (fun x => ptr (inr (inr x)))
                                   (inl (env, l0))
                      | S m' =>
                        apply (fun x => ptr (inr x)) (inl (env,m', l0))
                      end)) ->
    (forall l, @equiv state _ step (apply (fun x => ptr (inr (inr x))) (inl (env, l))) (e l)) ->
    @equiv state _ step (apply ptr (inl env)) (readL e l0 n).
Proof.
  intros.
  eapply EquivBind.
  - apply H0.
  - clear H0.
    unfold readL.
    revert l0.
    induction n; intros.
    + auto.
    + eapply EquivEff.
      rewrite H.
      reflexivity.
      intros. simpl.
      apply (IHn (l0 ++ [x])).
Qed.

Lemma print_derive :
  forall state step A ty_env
         (ptr : ty_env + (ty_env * nat * list nat + (ty_env + A)) -> state)
         l e env,
    step (apply ptr (inl env))
    = Some (existT _ _
                   (inr (bindE l),
                    fun l0 =>
                      match l0 with
                      | [] => apply (fun x => ptr (inr (inr x)))
                                    (inl env)
                      | n::l' => apply (fun x => ptr (inr x))
                                       (inl (env,n,l'))
                      end)) ->
    (forall l0 n,
        step (apply (fun x => ptr (inr x)) (inl (env,n,l0)))
        = Some (existT _ _
                       (inl (putE n),
                        fun _ =>
                          match l0 with
                          | [] => apply (fun x => ptr (inr (inr x)))
                                        (inl env)
                          | n'::l' => apply (fun x => ptr (inr x))
                                            (inl (env,n',l'))
                          end))) ->
    @equiv state _ step (apply (fun x => ptr (inr (inr x))) (inl env)) e ->
    @equiv state _ step (apply ptr (inl env)) (printL e l).
Proof.
  intros.
  unfold printL.
  eapply EquivBind.
  - eauto.
  - clear H. induction l.
    + eauto.
    + eapply EquivEff; eauto.
Qed.

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


Ltac make_env_f env x :=
  let ty_x := type of x in
  let rec aux env ctx :=
      lazymatch env with
      | x => constr:(fun x:ty_x => ctx x)
      | (?env',x) => constr:(fun x:ty_x => ctx (env',x))
      | (?env',?y) => aux env' open_constr:(fun e => ctx (e,y))
      end
  in
  aux env open_constr:(fun x => x).

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
    eapply (@EquivStateSkip _ _ (step_f f) nextptr (ptr env))
  end.

Ltac is_concr_nat n :=
  match n with
  | S ?n' => is_concr_nat n'
  | O => idtac
  end.

Ltac dest_sum :=
  let e := open_constr:(_|||_) in
  match goal with
  | |- ?g (inl _) = _ => unify g e
  | |- ?g (inr _) = _ => unify g e
  end.

Ltac dest_step :=
  repeat match goal with
           |- context[apply ?f _] => rewrite (apply_def f)
         end;
  simpl;
  repeat (dest_sum; simpl);
  unify_fun.

Definition thm (A:Type)(H:A) := tt.

Ltac derive_lemmas l := repeat
  lazymatch l with
  | [] => idtac
  | thm ?H::?l' =>
    try (eapply H; intros; try dest_step); derive_lemmas l'
  end.

Ltac derive_step :=
  lazymatch goal with
    |- @equiv ?state ?a ?step (apply ?ptr (inl ?env)) ?prog =>
    let ty_env := type of env in
    lazymatch prog with
      | (match ?m with | O => _ | S _ => _ end) =>
        let env' := (eval simpl in env) in
        let env0 := env_subst env' m 0 in
        eapply (EquivStateSkip
                  (next := match m with
                           | O =>
                             apply (fun x => ptr (inr (inl x))) (inl env0)
                           | S m' =>
                             apply (fun x => ptr (inr (inr x))) (@inl nat _ _)
                           end));
        [ dest_step
        | destruct m
        ]
      | let (_,_) := ?z in _ =>
        replace z with (fst z, snd z) by (destruct z; auto)
      | _ =>
      let p := leftmost prog in
      tryif is_fix p then
        (eapply EquivStateSkip;
         [ dest_step
         | progress repeat match goal with H : _ |- _ => refine (H _) || eapply H end])
        || (
          let env' := (eval simpl in env) in
          let m := match prog with _ ?k => k end in
          let env_f' := make_env_f env' m in
          let env_f := eval simpl in env_f' in
          let k := fresh in
          let rec generalize_args e :=
              lazymatch e with
              | ?e' m =>
                tryif
                    lazymatch env' with
                    | context[m] =>
                      match p with context[m] => idtac end
                    | _ => idtac end
                then
                  match type of m with
                  | nat =>
                    eapply (EquivGeneralize
                              (x0 := m)
                              (f := fun k:nat =>
                                      match m with
                                      | O =>
                                        apply (fun x => ptr (inr (inl x)))
                                              (inl (env_f 0,k))
                                      | S m' =>
                                        apply (fun x => ptr (inr (inr x)))
                                              (inl (env_f m', k))
                                      end))
                  | list ?A =>
                    eapply (EquivGeneralize
                              (x0 := m)
                              (f := fun l:list nat =>
                                      match m with
                                      | [] =>
                                        apply (fun x => ptr (inr (inl x)))
                                              (inl (env_f [],l))
                                      | a::l' =>
                                        apply (fun x => ptr (inr (inr x)))
                                              (inl (env_f l',l))
                                      end))
                  end;
                  [ dest_step
                  | match goal with
                      |- ?e ?x = ?f ?x =>
                      match eval pattern x in f with
                        ?g _ => exact (eq_refl: e x = (fun y => g y x) x)
                      end
                    end
                  | let m' := fresh m "n'" in
                    induction m as [|m'];
                    intro k;
                    simpl
                  ]
                else
                  generalize_args e'
              | ?e' ?x =>
                eapply (EquivGeneralize
                          (x0 := x)
                          (f := fun k:nat =>
                                  match m with
                                  | O =>
                                    apply (fun y => ptr (inr (inl y)))
                                          (inl (env_f 0,k))
                                  | S m' =>
                                    apply (fun y => ptr (inr (inr y)))
                                          (inl (env_f m', k))
                                  end));
                [ dest_step
                | generalize x;
                  intros;
                  lazymatch goal with
                    |- _ ?x = _ =>
                    pattern_rhs x;
                    try apply eq_refl
                  | _ => idtac
                  end
                | let m' := fresh m "m'" in
                  induction m as [|m'];
                  intro k
                ]
              | _ =>
                match type of m with
                | nat =>
                  eapply (EquivStateSkip
                            (next := match m with
                                     | O => apply (fun x => ptr (inr (inl x)))
                                                  (inl (env_f 0))
                                     | S m' => apply (fun x => ptr (inr (inr x)))
                                                     (inl (env_f m'))
                                     end))
                | list ?A =>
                  eapply (EquivStateSkip
                            (next := match m with
                                     | [] => apply (fun x => ptr (inr (inl x)))
                                                   (inl (env_f []))
                                     | x::l'=> apply (fun x => ptr (inr (inr x)))
                                                     (inl (env_f l',x))
                                     end))
                end;
                [ dest_step
                | let m' := fresh "n'" in
                  match type of m with
                  | nat =>
                    induction m as [|m']
                  | list nat =>
                    let a := fresh "a" in
                    induction m as [|a m']
                  end
                ]
              end
          in
          generalize_args prog
        )
     else idtac

    end
  end.

Ltac derive env :=
  repeat eexists;
  let e := open_constr:(apply (fun x => x) (inl env)) in
  match goal with
    |- equiv _ ?init _ => unify init e
  end;
  unshelve (repeat (derive_lemmas [thm get_derive; thm put_derive; thm EquivPure; thm print_derive; thm read_derive]; derive_step));
  try exact (fun _ => None); try exact unit.

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
  derive tt.
Defined.


Definition ex3 : t effect unit :=
  n <- get; ex3' 5 n.

Definition ex3_derive :
  {state & {step & {init | @equiv state _ step init ex3 }}}.
Proof.
  unfold ex3, ex3'.
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
              | S k' => put n; g k'
              end) x
       end) n.

Definition double_loop_derive :
  {state & {step & {init | @equiv state _ step init double_loop}}}.
Proof.
  unfold double_loop.
  derive tt.
Defined.

Eval cbv [double_loop double_loop_derive sum_merge prod_curry projT1 projT2] in (projT1 (projT2 double_loop_derive)).

Fixpoint ex_list (l : list nat) : t effect unit :=
  match l with
  | [] => put 0; Pure _ tt
  | x::rest =>
    put x;
      ex_list rest
  end.

Definition ex_list_derive :
  {state & {step & forall l, {init | @equiv state _ step init (ex_list l)}}}.
Proof.
  unfold ex_list.
  derive l.
Defined.

Definition ex_read_print :=
  n <- get;
    l <- read n;
    print l;
    put 0;
    Pure _ tt.

Definition ex_read_print_derive :
  {state & {step & {init | @equiv state _ step init ex_read_print}}}.
Proof.
  unfold ex_read_print.
  derive tt.
Defined.

Definition ex_read_print2 :=
  n <- get;
    l <- read n;
    print l;
    print l;
    Pure _ tt.


Definition ex_read_print2_derive :
  {state & {step & {init | @equiv state _ step init ex_read_print2}}}.
Proof.
  unfold ex_read_print2.
  derive tt.
Defined.


Parameter generateKey : unit -> list nat * list nat.
Parameter open : list nat -> list nat -> list nat -> list nat.
Parameter seal : list nat -> list nat -> list nat -> list nat.

Fixpoint splitAt A n (l : list A) :=
  match n with
  | O => ([], l)
  | S n' =>
    match l with
    | [] => ([], [])
    | x::l' =>
      let (l1,l2) := splitAt n' l' in
      (x::l1, l2)
    end
  end.

Definition ex_prod :=
  n <- get;
    l <- read n;
    let (l0,l1) := splitAt (Nat.div2 n) l in
    print l0;
      Pure _ tt.

Definition ex_prod_derive :
  {state & {step & {init | @equiv state _ step init ex_prod}}}.
Proof.
  unfold ex_prod.
  derive tt.
Defined.

Require String.
Open Scope string_scope.

Fixpoint simulatorS (n:nat) state (step : state -> step_range state)(init : state)(input : list nat)(accum : list nat) : list nat + String.string :=
    match n with
  | 0 => inr "not enough fuel"
  | S n' =>
      match step init with
      | Some (existT _ x ((e, next) as p)) =>
          match e with
          | inl e0 =>
              match
                e0 in (effect T)
                return
                  ((effect T + aux_effect T) * (T -> state) ->
                   (T -> state) -> list nat + String.string)
              with
              | getE _ =>
                  fun (_ : (effect nat + aux_effect nat) * (nat -> state))
                    (next0 : nat -> state) =>
                  match input with
                  | [] => inr "not enough input"
                  | n0 :: input0 => simulatorS n' step (next0 n0) input0 accum
                  end
              | putE n0 =>
                  fun (_ : (effect unit + aux_effect unit) * (unit -> state))
                    (next0 : unit -> state) =>
                  simulatorS n' step (next0 tt) input (n0 :: accum)
              end p next
          | inr a =>
              match
                a in (aux_effect T)
                return
                  ((effect T + aux_effect T) * (T -> state) ->
                   (T -> state) -> list nat + String.string)
              with
              | @bindE T t0 =>
                  fun (_ : (effect T + aux_effect T) * (T -> state))
                    (next0 : T -> state) =>
                  simulatorS n' step (next0 t0) input accum
              | skipE _ =>
                  fun (_ : (effect unit + aux_effect unit) * (unit -> state))
                    (next0 : unit -> state) =>
                  simulatorS n' step (next0 tt) input accum
              end p next
          end
      | None => inl accum
      end
  end.

Fixpoint simulatorE (e : t effect unit)(input accum : list nat) :=
  match e with
  | Pure _ _ => inl accum
  | Eff (getE _) prog =>
    match input with
    | [] => inr "not enough input"
    | n::rest => simulatorE (prog n) rest accum
    end
  | Eff (putE n) prog =>
    simulatorE (prog tt) input (n::accum)
  end.

Definition equiv' state (step : state -> step_range state) init prog :=
  forall input, exists fuel,
      simulatorS fuel step init input [] = simulatorE prog input [].

Theorem equiv_equiv' : forall state (step : state -> step_range state) init prog,
    equiv step init prog -> equiv' step init prog.
Proof.
  unfold equiv'.
  intros.
  generalize (@nil nat) as accum.
  revert input.
  induction H; intros.
  - destruct e.
    + destruct input.
      * exists 1.
        simpl.
        rewrite H.
        reflexivity.
      * destruct (H1 n input accum).
        exists (S x).
        simpl.
        rewrite H.
        auto.
    + destruct (H1 tt input (n::accum)).
      exists (S x).
      simpl.
      rewrite H.
      auto.
  - destruct (IHequiv input accum).
    exists (S x).
    simpl.
    rewrite H.
    auto.
  - destruct (IHequiv input accum).
    exists (S x).
    simpl.
    rewrite H.
    auto.
  - exists 1.
    simpl.
    rewrite H.
    auto.
Qed.


Theorem equiv'_equiv : forall state (step : state -> step_range state) init prog,
    equiv' step init prog -> equiv step init prog.
Proof.
  unfold equiv'.
  generalize (@nil nat) as accum.
  intros.
  revert init accum H.
  induction prog; intros.
  - destruct (H []).
    clear H.
    revert init accum H0.
    simpl.
    induction x; simpl; intros.
    + discriminate.
    + destruct (step init) eqn:?.
      * destruct s,p.
        destruct s.
        destruct e.
        discriminate.
        admit.
        destruct a0.
        -- eapply EquivBind.
           apply Heqs.
           eapply IHx.
           eauto.
        -- replace s0 with (fun _:unit => s0 tt) in Heqs.
           eapply EquivStateSkip.
           destruct u.
           rewrite Heqs.
           reflexivity.
           eapply IHx.
           destruct u. apply H0.
           extensionality v. destruct v. auto.
      * apply EquivPure. auto.
  - destruct e.
    + simpl in H0. destruct u.
      eapply EquivEff.
      all: swap 1 2.
      intros.
      eapply H.
      intros.
      destruct (H0 (x::input)).
      admit.
      admit.
    + admit.
Admitted.

Definition handshake pk sk :=
  n <- get;
  m <- get;
  let (ourEphemeralPublic,ourEphemeralSecret) := generateKey tt in
  print ourEphemeralPublic;
    theirEphemeralPublic <- read n;
    theirHandshakeSealed <- read m;
    let theirHandshake :=
        open theirHandshakeSealed theirEphemeralPublic ourEphemeralSecret
    in
    let (theirPK,theirHandshakeRest) := splitAt n theirHandshake in
    let hs := open theirHandshakeRest theirPK ourEphemeralSecret in
    let ourHandshake :=
        pk ++ seal (ourEphemeralPublic ++ theirEphemeralPublic) theirEphemeralPublic sk
    in
    print (seal ourHandshake theirPK ourEphemeralSecret);
      Pure _ tt.

Definition handshake_derive :
  {state & {step & forall pk sk, {init | @equiv state _ step init  (handshake pk sk)}}}.
Proof.
  unfold handshake.
  repeat eexists.
  derive (pk,sk).
Defined.

Eval cbv [handshake_derive handshake projT2 projT1] in projT1 handshake_derive.

Definition handshake_step :=
  Eval cbv [handshake_derive handshake projT2 projT1 sum_merge prod_curry] in projT1 (projT2 handshake_derive).

Require Import Extraction.

Extraction Language Haskell.

Extract Inductive unit => "()" [ "()" ].
Extract Inductive list => "([])" ["[]" "(:)"].
Extract Inductive bool => "Bool" ["True" "False"].
Extract Inductive prod => "(,)"  [ "(,)" ].
Extract Inductive sum => "Either" ["Left" "Right"].
Extract Inductive option => "Maybe" ["Just" "Nothing"].
Extract Inductive nat => Int ["0" "succ"] "(\fO fS n -> if n == 0 then fO () els e fS (n-1))".

Extraction "Handshake.hs" handshake_step.