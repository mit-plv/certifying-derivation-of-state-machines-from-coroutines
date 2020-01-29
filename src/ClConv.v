Require String.
Import String.StringSyntax.
Require Import List FunctionalExtensionality Arith.
Require Import StateMachines.Inhabit StateMachines.Foldable.
Import ListNotations.
Set Universe Polymorphism.
Open Scope type_scope.
Open Scope string_scope.
Set Implicit Arguments.

Arguments existT {_ _} _ _.

Section Effect.
  Context (eff : Set)(args rets: eff -> Set)(ret_type : Set).

  Inductive t :=
  | Eff : forall (e : eff), args e -> (rets e -> t) -> t
  | Return : ret_type -> t.

  Definition step_type (state : Set) := state -> forall (e : eff),
      rets e -> (state * option { e : eff & args e }) + ret_type.

  Inductive equiv' (state : Set)(step : step_type state) :
    state -> t -> option { e : eff & args e } -> Prop :=
  | Equiv'Eff : forall s e (a : args e) p next op,
      (forall r, equiv' step (next r) (p r) (op r)) ->
      (forall r, step s e r = inl (next r, op r)) ->
      equiv' step s (Eff a p) (Some (existT _ a))
  | Equiv'Return : forall s o,
      step s = (fun _ _ => inr o) ->
      equiv' step s (Return o) None.

  Definition equiv state (step : step_type state) init p :=
    exists op s, step init = (fun _ _ => inl (s, op)) /\ equiv' step s p op.

End Effect.

Inductive effect := getNat | putNat | getString | putString | getRand.

Scheme Equality for effect.

Definition args_effect (e : effect) :=
  match e with
  | getNat => unit
  | putNat => nat
  | getString => unit
  | putString => String.string
  | getRand => unit
  end.

Definition rets_effect (e : effect) :=
  match e with
  | getNat => nat
  | putNat => unit
  | getString => String.string
  | putString => unit
  | getRand => list Ascii.ascii
  end.

Inductive yield_effect := yield : yield_effect.

Notation "'const_yield' A" :=
  (fun _:yield_effect => A)
    (at level 10).

Class is_eff eff :=
  { args : eff -> Set;
    rets : eff -> Set;
    lift_eff : forall A B (e : eff)(_:rets e -> A + option B)(e0:eff),
        rets e0 -> A + option B }.

Definition equiv_coro A B state
           (step : step_type (const_yield A)(const_yield B) unit state) init p :=
  exists op s, forall r,
      step init yield r = inl (s r, op r)
      /\ equiv' (ret_type := unit) step (s r) (p r) (op r).

Definition seqE (A B C:Set) (e : t (const_yield A) (const_yield B) unit)
  : (A -> (B -> t (const_yield A) (const_yield B) unit) ->
     t args_effect rets_effect (option C)) ->
    t args_effect rets_effect (option C) :=
  match e with
  | Return _ _ c => fun _ => Return _ _ None
  | Eff _ a p => fun cont => cont a p
  end.

Definition coro_type A B state
           (_ : step_type (const_yield A) (const_yield B) unit state):=
  B -> t (const_yield A)(const_yield B) unit.

Definition proc_coro (A B C state : Set)
           (step : step_type (const_yield A)(const_yield B) unit state)
           (c : coro_type step) (x : B)
  : (A -> coro_type step -> t args_effect rets_effect (option C)) ->
    t args_effect rets_effect (option C) :=
  seqE (c x).


Fixpoint bind (T S eff : Set)(args rets : eff -> Set)
         (x : t args rets T)(p : T -> t args rets S) :=
  match x with
  | Return _ _ v => p v
  | Eff e a q => Eff e a (fun b => bind (q b) p)
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
  (proc_coro c x (fun n c => e))
    (at level 100, right associativity).
Notation "v1 <- 'yield' v2 ; e" :=
  (Eff yield v2 (fun v1 => e))
    (at level 100, right associativity).
Notation "x <- 'getRnd' ; e" :=
  (Eff getRand (tt : args_effect getRand) (fun x : rets_effect getRand => e))
    (at level 100, right associativity).
Notation "x <<- p ; e" :=
  (bind p (fun x => e))
    (at level 100, right associativity).

Definition get_put : t args_effect rets_effect nat :=
  n <- getN;
  putN (S n);
  Return _ _ (S n).

Definition seqE' A C state
           (x : (state * option { e : yield_effect & A }) + unit)
           (f : state -> A -> t args_effect rets_effect C)
           (f0 : t args_effect rets_effect C) :=
  match x with
  | inl (s, Some (existT _ v)) => f s v
  | _ => f0
  end.

Definition sum_merge (A B C : Set)(f : A -> C)(g : B -> C)(x : sum A B) :=
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
  lazymatch goal with
    |- _ = ?X =>
    let X' := (eval pattern term in X) in
    change X with X'
  end.

Lemma equal_f : forall (A B : Set)(f g : A -> B) x,
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
            change X with ((fun _:unit => X) tt)
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

Definition nat_rect_nondep A f (f0 : nat -> A -> A) :=
  fix F (n : nat) : A :=
    match n with
    | O => f
    | S n' => f0 n' (F n')
    end.

Definition list_rec_nondep A B fnil fcons :=
  fix aux (l:list A) : B :=
    match l with
    | [] => fnil
    | x::xs => fcons x xs (aux xs)
    end.


Definition ex_coroutine k n : t (const_yield nat) (const_yield nat) unit :=
  m <- yield (k + n)%nat;
    _ <- yield (n + m)%nat;
    Return _ _ tt .

Ltac st_op_to_ev :=
  lazymatch goal with
    |- equiv' ?step ?st ?prog ?op =>
    lazymatch st with
    | ?f _ _ =>
      let u := open_constr:(fun r c => _) in
      unify f u;
      lazymatch op with
      | ?g _ _ =>
        let u := open_constr:(fun r c => _) in
        unify g u
      end
    | ?f _ =>
      let u := open_constr:(fun r => _) in
      unify f u;
      lazymatch op with
      | ?g _ =>
        let u := open_constr:(fun r => _) in
        unify g u
      end
    | _ => idtac
    end;
    cbv beta
  end.

Lemma derive_parent_rect : forall state A C N (a0:A) f f0 st0 stS op0 opS step,
    (forall a, equiv' step (st0 a) (f a a) (op0 a)) ->
    (forall N0,
        (forall a, equiv' step (match N0 with O => st0 a | S N0' => stS a N0' end) (nat_rect_nondep (f a) (f0 a) N0 a) (match N0 with O => op0 a | S N0' => opS a N0' end)) ->
        (forall a, equiv' step (stS a N0)
                          (f0 a N0
                              (nat_rect_nondep
                                    (f a) (f0 a)
                                    N0) a) (opS a N0))) ->
    @equiv' _ args_effect rets_effect C state step (match N with O => st0 a0 | S N0 => stS a0 N0 end) (nat_rect_nondep (f a0) (f0 a0) N a0) (match N with O => op0 a0 | S N0 => opS a0 N0 end).
Proof.
  intros.
  revert a0.
  induction N; intros; simpl; auto.
Qed.

Lemma derive_list_rec : forall state A B C (l : list B)(a0:A) f f0 st0 stS op0 opS step,
    (forall a, equiv' step (st0 a) (f a a) (op0 a)) ->
    (forall b0 l0,
        (forall a,
            equiv' step
                   (match l0 with [] => st0 a | b::l' => stS a b l' end)
                   (list_rec_nondep (f a) (f0 a) l0 a)
                   (match l0 with [] => op0 a | b::l' => opS a b l' end)) ->
        (forall a, equiv' step (stS a b0 l0)
                          (f0 a b0 l0
                              (list_rec_nondep
                                 (f a) (f0 a)
                                 l0) a) (opS a b0 l0))) ->
    @equiv' _ args_effect rets_effect C state step
            (match l with [] => st0 a0 | b::l' => stS a0 b l' end)
            (list_rec_nondep (f a0) (f0 a0) l a0)
            (match l with [] => op0 a0 | b::l' => opS a0 b l' end).
Proof.
  intros.
  revert a0.
  induction l; intros; simpl; auto.
Qed.

Lemma derive_opt : forall eff args rets A C state (x : option A) sta st fa f opa op step,
    (forall a, equiv' step (sta a) (fa a) (opa a)) ->
    equiv' step st f op ->
    @equiv' eff args rets C state step
           (match x with Some a => sta a | None => st end)
           (match x with Some a => fa a | None => f end)
           (match x with Some a => opa a | None => op end).
Proof.
  intros.
  destruct x; auto.
Qed.

Lemma derive_bool : forall eff args rets C state (b:bool) stt stf ft ff opt opf step,
    equiv' step stt ft opt ->
    equiv' step stf ff opf ->
    @equiv' eff args rets C state step (if b then stt else stf)
            (if b then ft else ff) (if b then opt else opf).
Proof.
  intros.
  destruct b; auto.
Qed.

Lemma derive_sum : forall eff args rets A B C state (x : A + B) fa fb sta stb opa opb step,
    (forall a, equiv' step (sta a) (fa a) (opa a)) ->
    (forall b, equiv' step (stb b) (fb b) (opb b)) ->
    @equiv' eff args rets C state step (match x with
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

Lemma derive_seqE' :
  forall A C state state'
         (x : (state' * option { _ : yield_effect & A }) + unit)
         f f0 g g0 h h0 step,
    (forall s v, equiv' step (g s v) (f s v) (h s v)) ->
    equiv' step g0 f0 h0 ->
    @equiv' _ _ _ C state step
            (match x with
             | inl (s, Some (existT _ v)) => g s v
             | _ => g0
             end) (seqE' x f f0)
            (match x with
             | inl (s, Some (existT _ v)) => h s v
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

Definition step_state (A B C state : Set)
           (step : step_type (const_yield A)(const_yield B) unit state) st x g :=
  seqE' (step st yield x) (fun s v => g v s) (Return _ _ (@None C)).

Lemma equal_f_dep : forall A (T : A -> Set) B (f g : forall a, T a -> B) a0,
    f = g -> f a0 = g a0.
Proof.
  intros.
  rewrite H.
  auto.
Qed.

Ltac next_ptr :=
  lazymatch goal with
    |- @equiv' _ _ _ _ ?st _ _ _ _ =>
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

Definition lift_effect A B(e : effect)(a : rets_effect e -> A + option B)(e0 : effect)
  : rets_effect e0 -> A + option B :=
  match
  e as e1
  return ((rets_effect e1 -> A + option B) -> rets_effect e0 -> A + option B)
  with
  | getNat =>
    fun a0 : rets_effect getNat -> A + option B =>
      match e0 as e1 return (rets_effect e1 -> A + option B) with
      | getNat => a0
      | _ => fun _ => inr None
      end
  | putNat =>
    fun a0 : rets_effect putNat -> A + option B =>
      match e0 as e1 return (rets_effect e1 -> A + option B) with
      | putNat => a0
      | _ => fun _ => inr None
      end
  | getString =>
    fun a0 : rets_effect getString -> A + option B =>
      match e0 as e1 return (rets_effect e1 -> A + option B) with
      | getString => a0
      | _ => fun _ => inr None
      end
  | putString =>
    fun a0 : rets_effect putString -> A + option B =>
      match e0 as e1 return (rets_effect e1 -> A + option B) with
      | putString => a0
      | _ => fun _ => inr None
      end
  | getRand =>
    fun a0 : rets_effect getRand -> A + option B =>
      match e0 as e1 return (rets_effect e1 -> A + option B) with
      | getRand => a0
      | _ => fun _ => inr None
      end
  end a.

Instance effect_is_eff : is_eff effect :=
  { args := args_effect;
    rets := rets_effect;
    lift_eff := lift_effect }.

Ltac dest_step' :=
  lazymatch goal with
    |- @eq (?T1 + ?T2) (?g _ ?ef ?r) _ =>
    pattern_rhs r;
      apply equal_f;
      lazymatch goal with
        |- _ = ?rhs =>
        lazymatch ef with
          (*
        | putNat =>
          change rhs with
          ((fun e => match e as e0 return rets_effect e0 -> T1+T2 with
                     | putNat => rhs
                     | _ => fun _ => inr None
                     end) ef)
        | getNat =>
          change rhs with
          ((fun e => match e as e0 return rets_effect e0 -> T1+T2 with
                     | getNat => rhs
                     | _ => fun _ => inr None
                     end) ef)
        | putString =>
          change rhs with
          ((fun e => match e as e0 return rets_effect e0 -> T1+T2 with
                                | putString => rhs
                                | _ => fun _ => inr None
                                end) ef)
        | getString =>
          change rhs with
          ((fun e => match e as e0 return rets_effect e0 -> T1+T2 with
                                | getString => rhs
                                | _ => fun _ => inr None
                                end) ef)
*)
        | yield =>
          (*
          let tmp := fresh in
          set (tmp := (fun _ => rhs yield));
          replace rhs with tmp by (unfold tmp; auto);
          subst tmp*)
          change rhs with ((fun _ => rhs) yield)
        | _ => change rhs with (lift_eff ef rhs ef)
        end
      end;
      (apply equal_f_dep || apply equal_f);
      simpl;
      repeat (dest_sum; simpl);
      unify_fun
  | |- _ ?r = _ => repeat (dest_sum; simpl); unify_fun
  end.

Definition label := fun _:nat => True.

Lemma bind_if : forall C D (b:bool)(p q : t args_effect rets_effect C)(r : C -> t args_effect rets_effect D),
  bind (if b then p else q) r
  = if b then bind p r else bind q r.
Proof.
  intros.
  destruct b; auto.
Qed.

Ltac derive_core ptr env :=
  st_op_to_ev;
  lazymatch goal with
    |- equiv' _ _ ?prog _ =>
    let fv := free_var prog env in
    lazymatch prog with
    | @Eff _ ?args ?rets ?C ?e _ _ =>
      eapply (Equiv'Eff (ptr (inl fv)) e);
      [ let H := fresh in
        intro H;
        derive_core (fun x => ptr (inr x)) (env,H)
       | intros; dest_step']
    | Return _ _ _ =>
      idtac
      (*
      eapply (Equiv'Return _ (ptr (inl fv)));
      intros; cbv beta; dest_step'
       *)
    | bind (if _ then _ else _) _ =>
      rewrite bind_if;
      simpl;
      derive_core ptr env
    | seqE' _ _ _ =>
      eapply (derive_seqE' _ (fun s v => _) (fun s v => _) (fun s v => _));
      [ let s := fresh in
        let v := fresh in
        intros s v;
        derive_core ptr (env,s,v)
      | let ptr := next_ptr in
        derive_core ptr env ]
    | (match ?x with inl _ => _ end) =>
      eapply (derive_sum _ _ _ (fun a => _) (fun b => _) (fun a => _) (fun b => _));
      [ let a := fresh in
        intro a;
        cbv beta;
        let ptr := next_ptr in
        derive_core ptr (env,a)
      | let b := fresh in
        intro b;
        cbv beta;
        let ptr := next_ptr in
        derive_core ptr (env,b)
      ]
    | (match ?x with Some _ => _ | None => _ end) =>
      eapply (derive_opt _ (fun a => _) (fun a => _) (fun a => _));
      [ let a := fresh in
        intro a;
        cbv beta;
        let ptr := next_ptr in
        derive_core ptr (env,a)
      | cbv beta;
        let ptr := next_ptr in
        derive_core ptr env
      ]
    | (if ?b then _ else _) =>
      eapply derive_bool;
      [ let ptr := next_ptr in
        derive_core ptr env
      | let ptr := next_ptr in
        derive_core ptr env
      ]
    | nat_rect_nondep _ _ _ _ =>
      (now (repeat match goal with
         | H : ?p |- _ => apply H
         end))
      ||
      (eapply (derive_parent_rect _ _ (fun a b => _) (fun a => _) (fun a => _));
       [ let a := fresh in
         intro a;
         cbv beta;
         let ptr := next_ptr in
         derive_core ptr (env,a)
       | let n := fresh in
         let H := fresh in
         let a := fresh in
         intros n H a;
         cbv beta;
         let ptr := next_ptr in
         derive_core ptr (env,n,a)
      ])
    | list_rec_nondep _ _ _ _ =>
      (now (repeat match goal with
                   | H : ?p |- _ => apply H
                   end))
      ||
      (eapply (derive_list_rec _ _ (fun _ _ => _) (fun _ => _) (fun _ => _));
       [ let a := fresh in
         intro a;
         cbv beta;
         let ptr := next_ptr in
         derive_core ptr (env,a)
       | let b := fresh in
         let l := fresh in
         let H := fresh in
         let a := fresh in
         intros b l H a;
         cbv beta;
         let ptr := next_ptr in
         derive_core ptr (env,b,l,a)
       ])
    end
  end.

(*
Definition replace A i l (a:A) :=
  (fix aux i l pre :=
    match l with
    | [] => []
    | x::l' =>
      match i with
      | O => pre ++ a :: l'
      | S i' => aux i' l' (pre ++ [x])
      end
    end) i l [].*)

Definition pipe A B (a : A)(f : A -> B) := f a.

Instance coro_type_inhabitant A B state step :
  Inhabit (@coro_type A B state step) :=
  { inhabitant := fun _ => Return _ _ inhabitant }.

Instance t_inhabitant e a r (c:Set) `{IC : Inhabit c} : Inhabit (@t e a r c) :=
  { inhabitant := Return _ _ inhabitant }.

Definition seq_abs A B R state
           (step : step_type (const_yield A)(const_yield B) R state) (x:B) C (_:C) (g : A -> C -> t args_effect rets_effect R ) := t_inhabitant.


Opaque dummy.

Definition equiv_coro' (A B C :Set) `{IA : Inhabit A} `{IB : Inhabit B} state
           (step : step_type _ _ C state)
           st
           (coro : B -> t (const_yield A) (const_yield B) C) :=
  exists op, equiv' step st (r <- yield inhabitant; coro r) op.

Ltac get_init c :=
  let init := open_constr:(_) in
  let _ := constr:(ltac:(auto with equivc) : equiv_coro' _ init c) in
  init.

Ltac opt_match_fun expr :=
  lazymatch expr with
  | (match ?o with Some a => _ | None => _ end) =>
    lazymatch (eval pattern o in expr) with
    | ?F _ =>
      eval cbv beta iota in (fun a => F (Some a))
    end
  end.

Definition option_branch A B (f:A -> B) f0 o :=
  match o with
  | Some a => f a
  | None => f0
  end.

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
  | @Eff _ args_effect rets_effect ?C ?e ?a ?f =>
    let x := (eval cbv beta in (f (dummy _ _ i))) in
    let d := to_dummy (S i) x in
    lazymatch (eval pattern (dummy _ (rets_effect e) i) in d) with
    | ?g _ =>
      constr:((@Eff _ args_effect rets_effect C e a, g))
    end
  | @proc_coro ?A ?B ?C ?state ?step ?c ?z ?f =>
    let x := (eval cbv beta in (f (dummy _ _ i) (dummy _ _ (S i)))) in
    lazymatch f with
    | context [proc_coro] =>
      let d := to_dummy (S (S i)) x in
      lazymatch type of f with
      | _ -> ?T -> _ =>
        lazymatch (eval pattern (dummy _ A i), (dummy _ T (S i)) in d) with
        | ?g _ _ =>
          constr:((@seq_abs A B C state step z (coro_type step) c, g))
        end
      end
    | _ =>
      constr:((@seq_abs A B C state step z (coro_type step) c, f))
    end
  | (match ?o with Some _ => _ | None => ?f0 end) =>
    let f := opt_match_fun p in
    lazymatch type of o with
    | option ?A =>
      let B := type of p in
      let x := (eval cbv beta in (f (dummy _ _ i))) in
      let d := to_dummy (S i) x in
      let d0 := to_dummy i f0 in
      lazymatch (eval pattern (dummy _ A i) in d) with
      | ?g _ =>
        constr:((@option_branch A B, g, d0, o))
      end
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

Ltac reconstruct tree i :=
  lazymatch tree with
  | (pipe, ?init, ?f) =>
    let x := (eval cbv beta in (f init)) in
    reconstruct x i
  | (Eff ?e ?a, ?p) =>
    let x := (eval cbv beta in (p (dummy _ _ i))) in
    let p' := reconstruct x (S i) in
    lazymatch type of p with
    | ?ty -> _ =>
      lazymatch (eval pattern (dummy _ ty i) in p') with
      | ?p'' _ =>
        constr:(Eff e a p'')
      end
    end
  | (@seq_abs ?A ?B ?C _ ?step ?z ?state ?st, ?p) =>
    let x := (eval cbv beta in (p (dummy _ _ i) (dummy _ _ (S i)))) in
    let p' := reconstruct x (S (S i)) in
    lazymatch (eval pattern (dummy _ A i), (dummy _ state (S i)) in p') with
    | ?p'' _ _ =>
      constr:(@step_state A B C _ step st z p'')
    end
  | (@option_branch ?A ?B, ?f, ?f0, ?o) =>
    let x := (eval cbv beta in (f (dummy _ _ i))) in
    let p' := reconstruct x (S i) in
    lazymatch (eval pattern (dummy _ A i) in p') with
    | ?p'' _ =>
      constr:(@option_branch A B p'' f0 o)
    end
  | (@nat_rect_nondep ?A, ?f, ?f0, ?n, ?a) =>
    let x := (eval cbv beta in (f (dummy _ _ i))) in
    let y := (eval cbv beta in (f0 (dummy _ _ i) (dummy _ _ (S i)) (dummy _ _ (S (S i))))) in
    let f' := reconstruct x (S i) in
    let f0' := reconstruct y (S (S (S i))) in
    let ty := type of a in
    lazymatch (eval pattern (dummy _ ty i) in f') with
    | ?f'' _ =>
      lazymatch (eval pattern (dummy _ nat i), (dummy _ A (S i)), (dummy _ ty (S (S i))) in f0') with
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
      reconstruct y 0
    end
  end.

Transparent proc_coro.

(*
Definition loop_ex (n i : nat)(g : forall A, A -> t args_effect rets_effect) :=
  pipe (ex_coroutine 0 : coro_type (projT1 (projT2 ex_coroutine_derive')))
       (fun c0 =>
          nat_rect_nondep
            (fun l =>
               option_branch
                        (fun c => g _ c)
                        (Done _ _)
                        (nth_err _ l i))
            (fun m rec l =>
               pipe (ex_coroutine m : coro_type (projT1 (projT2 ex_coroutine_derive')))
                    (fun cm =>
                       rec (cm::l)))
            n [c0]).
*)
Ltac get_step c :=
  let step := open_constr:(_) in
  let _ := constr:(ltac:(auto with equivc') : equiv_coro' step _ c) in
  step.

Ltac derive_coro env :=
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
  lazymatch goal with
    |- _ ?init _ =>
    let u := open_constr:(inl env) in
    unify init u
  end;
  let r := fresh in
  repeat eexists; try econstructor;
  [ intro r; derive_core open_constr:(fun x => inr x) (env,r)
  | intros; dest_step'
  ];
  let ptr := next_ptr in
  lazymatch goal with
    |- equiv' _ _ (Return _ _ ?r) _ =>
    eapply (Equiv'Return _ (ptr r));
    simpl;
    lazymatch goal with
      |- _ ?a = _ =>
      pattern_rhs a; apply eq_refl
    end
  | _ => idtac
  end.

Lemma ex_coroutine_derive :
  { state & { step & forall k, { init | @equiv_coro' _ _ _ _ _ state step init (ex_coroutine k) }}}.
  do 3 eexists.
  derive_coro (tt,k).
Defined.

Definition ex_coroutine_step :=
  projT1 (projT2 ex_coroutine_derive).

Definition ex_coroutine_equiv k :
  equiv_coro' ex_coroutine_step _ (ex_coroutine k) :=
  proj2_sig (projT2 (projT2 ex_coroutine_derive) k).

Definition ex_coroutine_equiv' k
  : equiv_coro' ltac:(let x := eval simpl in (projT1 (projT2 ex_coroutine_derive)) in exact x) ltac:(let x := eval simpl in (proj1_sig (projT2 (projT2 ex_coroutine_derive) k)) in exact x) (ex_coroutine k) :=
  ex_coroutine_equiv k.

Hint Resolve ex_coroutine_equiv ex_coroutine_equiv' : equivc.
Hint Resolve ex_coroutine_equiv : equivc'.

Lemma GenForall2_nth_Some_list_equiv_coro :
  forall (A B:Set) (IA : Inhabit A) (IB : Inhabit B) state
         (step : step_type (const_yield A) (const_yield B) unit state)
         x1 x2 n a1 a2,
    GenForall2 (F := list)(fun (coro : coro_type step) (st : state) =>
                  equiv_coro' step st coro) x1 x2 ->
    nth_err _ x1 n = Some a1 ->
    nth_err _ x2 n = Some a2 ->
    equiv_coro' step a2 a1.
Proof.
  intros.
  eapply (GenForall2_nth_Some (F := list)(R := (fun (coro : coro_type step) (st : state) => equiv_coro' step st coro))); eauto.
Qed.

Hint Resolve GenForall2_nth_Some_list_equiv_coro : foldable.

Ltac generalize_and_ind :=
  lazymatch goal with
    |- nat_rect_nondep _ _ ?k ?l = nat_rect_nondep _ _ _ ?l' =>
    lazymatch type of l with
    | context [@coro_type _ _ ?state ?step] =>
        cut (GenForall2 (fun (coro : coro_type step) (st : state) => equiv_coro' step st coro) l l');
      [ generalize l l'
       |unfold GenForall2; eexists; split; [reflexivity|simpl; eauto with equivc]];
      induction k; intros;
      lazymatch goal with
        |- nat_rect_nondep ?f ?f0 _ _ = nat_rect_nondep ?f' ?f0' _ _ =>
        let tmp := fresh in
        set (tmp := f);
        let tmp' := fresh in
        set (tmp' := f');
        let tmp0 := fresh in
        set (tmp0 := f0);
        let tmp0' := fresh in
        set (tmp0' := f0');
        simpl nat_rect_nondep;
        subst tmp; subst tmp'; subst tmp0; subst tmp0';
        cbv beta
      end
    end
  end.

Ltac dest_yield :=
  repeat match goal with
         | e : yield_effect |- _ => destruct e
         end.

Ltac proc_step :=
  lazymatch goal with
    |- proc_coro ?c ?x ?f = step_state ?step ?st _ ?g =>
    let H := fresh in
    let H0 := fresh in
    assert (equiv_coro' step st c) as (H,H0) by eauto with foldable;
    let s := fresh "s" in
    let e := fresh "e" in
    let a := fresh "a" in
    let p := fresh "p" in
    let next := fresh "next" in
    let op := fresh "op" in
    let H1 := fresh in
    let H2 := fresh in
    inversion H0 as [s e a p next op H1 H2|];
    subst;
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
    end;
    dest_yield
  end.

Ltac dest_opt :=
  lazymatch goal with
    |- match ?o with _ => _ end = option_branch _ _ ?o0 =>
    destruct o eqn:?, o0 eqn:?;
             unfold option_branch
  end.

Notation "'let_coro' x := c 'in' p" :=
  (pipe (c : coro_type ltac:(let step := get_step c in exact step))
        (fun x => p))
    (at level 200, only parsing).

Ltac mid_eq_core :=
  generalize_and_ind
  || dest_opt
  || proc_step
  || (repeat match goal with
             | H : _ |- _ => apply H
             end;
      now eauto with foldable equivc)
  || (exfalso; now eauto with foldable)
  || reflexivity
  || lazymatch goal with
       |- Eff _ _ _ = Eff _ _ _ =>
       f_equal;
       let H := fresh in
       extensionality H
     end.

Definition loop_ex (n i : nat) :=
  let_coro c0 := ex_coroutine 0 in
      nat_rect_nondep
        (fun l =>
           match nth_err _ l i : option (@coro_type nat nat _ _) with
           | Some c =>
             r <- resume c $ 1;
               putN r;
               Return _ _ (Some tt)
           | None => Return _ _ None
           end)
        (fun m rec l =>
           putN (0:args_effect putNat);
             pipe (ex_coroutine m : @coro_type nat nat _ _)
                  (fun cm =>
                     rec (cm::l)))
        n [c0].

Ltac derive' env :=
  lazymatch goal with
    |- equiv _ ?init ?x =>
    let u := open_constr:(inl env) in
    unify init u;
    repeat eexists;
    [ dest_step'
    | unfold option_branch;
      derive_core open_constr:(fun a => inr a) env];
    let ptr := next_ptr in
    lazymatch goal with
      |- equiv' ?step _ (Return _ _ ?r) _ =>
      eapply (Equiv'Return _ (ptr r));
      simpl;
      lazymatch goal with
        |- _ ?x = _ =>
        pattern_rhs x;
        apply eq_refl
      | _ => apply eq_refl
      end
    end
      (*
      unshelve derive_core open_constr:(fun a => inr a) env;
      intros; exact inhabitant*)
  end.

Definition simple_double_loop : t args_effect rets_effect _ :=
  n <- getN;
    nat_rect_nondep
      (fun ls => Return _ _ (Some ls))
      (fun n' rec ls =>
         m <- getN;
         nat_rect_nondep
           (fun l => rec (l::ls))
           (fun m' rec' l =>
              k <- getN;
                rec' (k::l))
           m [])
      n [].

Definition simple_double_loop_derive :
  { state & { step & { init | @equiv _ _ _ _ state step init simple_double_loop}}}.
  do 3 eexists.
  unfold simple_double_loop.
  derive' tt.
Defined.


Eval cbv [projT1 projT2 simple_double_loop simple_double_loop_derive] in projT1 (projT2 simple_double_loop_derive).
Arguments Return {_ _ _ _ } _.

Definition list_ex :=
  n <- getN;
    list_rec_nondep
      (fun a => Return (Some a))
      (fun x l rec a =>
         putN 0;
         if Nat.even x then
           rec (a + x)%nat
         else
           Return (Some a))
      (seq 0 n) 0.

Definition list_ex_derive :
  { state & { step & { init | @equiv _ _ _ _ state step init list_ex}}}.
Proof.
  do 3 eexists.
  unfold list_ex.
  derive' tt.
Defined.

Definition simple_ex :=
  n <- getN;
    nat_rect_nondep
      (fun accum => Return (Some accum))
      (fun n' rec accum =>
         putN n'; rec (n' + accum)%nat)
      n 0.


Definition simple_ex_derive :
  { state & { step & { init | @equiv _ _ _ _ state step init simple_ex}}}.
  do 3 eexists.
  unfold simple_ex.
  derive' tt.
Defined.


Eval cbv [projT1 projT2 simple_ex simple_ex_derive sum_merge prod_curry] in projT1 (projT2 simple_ex_derive).

Definition dummy A (x : A) := True.

Ltac list_unify def :=
  lazymatch goal with
    def := ?l |- ?c =>
           let rec aux l :=
               tryif is_evar l then
                 let oc := open_constr:(c::_) in
                 unify l oc
               else
                 lazymatch l with
                 | _::?l' => aux l'
                 end
           in
           aux l
  end.

Ltac state_to_nat s :=
  lazymatch s with
  | inr ?s' =>
    let p := state_to_nat s' in
    lazymatch p with
      (?n,?v) =>
      constr:((S n, v))
    end
  | inl ?v => constr:((O,v))
  | ?v => constr:((O,v))
  end.

Ltac get_equalities l :=
  match goal with
  | _ : ?lhs = ?rhs |- _ =>
    get_equalities constr:((lhs = rhs) :: l)
  | _ => l
  end.

Ltac to_dot_core Heqp r :=
  lazymatch type of Heqp with
    _ = ?s0 =>
    clear Heqp;
    let p := state_to_nat s0 in
    lazymatch p with
      (?n0, ?v0) =>
      let ty := type of v0 in
      lazymatch goal with
        |- dummy (inl (?s', ?op)) =>
        let p := state_to_nat s' in
        lazymatch p with
          (?n, ?v) =>
          lazymatch goal with
          | EQR : r = ?r0 |- _ =>
            clear EQR;
            let eqs := get_equalities (@nil Prop) in
            lazymatch goal with
            | _ : dummy (n0, ty) |- _ =>
              idtac
            | _ => 
              assert (dummy (n0, ty));
              [ list_unify tt; exact I | ]
            end;
            change (dummy (n0, v0, r0, eqs, n, v, op));
            repeat match goal with
                     H : _ |- _ =>
                     lazymatch goal with
                       |- context[H] =>
                       revert H
                     end
                   end
          | _ =>
            let eqs := get_equalities (@nil Prop) in
            lazymatch goal with
            | _ : dummy (n0, ty) |- _ =>
              idtac
            | _ => 
              assert (dummy (n0, ty));
              [ list_unify tt; exact I | ]
            end;
            change (dummy (n0, v0, r, eqs, n, v, op));
            repeat match goal with
                     H : _ |- _ =>
                     lazymatch goal with
                       |- context[H] =>
                       revert H
                     end
                   end
          end
        end
      | |- dummy (inr ?o) =>
        lazymatch goal with
        | _ : dummy (n0, ty) |- _ =>
          idtac
        | _ => 
          assert (dummy (n0, ty));
          [ list_unify tt; exact I | ]
        end;
        change (dummy (n0, v0, o));
        repeat match goal with
                 H : _ |- _ =>
                 lazymatch goal with
                   |- context[H] =>
                   revert H
                 end
               end
      end
    end
  end.

Definition foo : list Prop.
Proof.
  evar (result : list Prop).
  assert (forall s e r, dummy (projT1 (projT2 simple_ex_derive) s e r)).
  intros.
  destruct s eqn:?; simpl.
  to_dot_core Heqp r.
  list_unify result.
  firstorder.
  destruct s0; simpl.
  destruct e.
  destruct r eqn:?.
  to_dot_core Heqp r.
  list_unify result.
  firstorder.
  to_dot_core Heqp r.
  list_unify result.
  firstorder.
  apply I.
  apply I.
  apply I.
  apply I.
  destruct s0; simpl.
  destruct p; simpl.
  destruct p; simpl.
  destruct e.
  apply I.
  destruct n0.
  to_dot_core Heqp r.
  list_unify result.
  firstorder.
  to_dot_core Heqp r.
  list_unify result.
  firstorder.
  apply I.
  apply I.
  apply I.
  to_dot_core Heqp r.
  list_unify result.
  firstorder.
  apply result.
  Grab Existential Variables.
  apply nil.
Defined.
Notation "<< x @ y @ .. @ z >>" :=
  (dummy (pair .. (pair x y) .. z)) (at level 0).
Eval cbv [foo] in foo.

Ltac derive env :=
  lazymatch goal with
    |- equiv _ ?init ?x =>
    let u := open_constr:(inl env) in
    unify init u;
    let H := fresh in
    assert (x = ltac:(let x' := eval red in x in
                          let x'' := coro_to_state x' in exact x''))
      as H by
         (change x with ltac:(let x0 := eval red in x in exact x0);
            unfold pipe;
            repeat mid_eq_core);
    rewrite H;
    clear H;
    unfold step_state;
    repeat eexists;
    [ dest_step'
    | unfold option_branch;
      derive_core open_constr:(fun a => inr a) env ];
    let ptr := next_ptr in
    lazymatch goal with
      |- equiv' ?step _ (Return ?r) _ =>
      eapply (Equiv'Return _ (ptr r));
      simpl;
      lazymatch goal with
        |- _ ?x = _ =>
        pattern_rhs x;
        apply eq_refl
      | _ => apply eq_refl
      end
    end
  end.


(*
Lemma loop_ex_eq k n :
  loop_ex k n =
  ltac:(let x := (eval red in (loop_ex k n)) in
        let x' := coro_to_state x in exact x').
Proof.
  unfold loop_ex.
  unfold pipe.
  repeat mid_eq_core.
Qed.
*)

Definition loop_ex_derive n i :
  { state & { step & { init | @equiv _ _ _ _ state step init (loop_ex n i) }}}.
Proof.
  do 3 eexists.
  unshelve derive (tt,n,i); exact unit.
Defined.

Eval cbv [projT1 projT2 loop_ex_derive] in (fun n i => projT1 (projT2 (loop_ex_derive n i))).

Definition simple_ret : t args_effect rets_effect nat :=
  n <- getN;
    if Nat.even n then
      Return 0
    else
      Return 1.

Definition simple_receive : t args_effect rets_effect (option unit) :=
  x <<- simple_ret;
    putN x;
    Return (Some tt).

Definition simple_derive :
  { state & { step & { init | @equiv _ _ _ _ state step init simple_receive }}}.
Proof.
  do 3 eexists.
  unfold simple_receive, simple_ret.
  simpl.
  derive' tt.
Defined.

(*
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

Lemma GenForall2_bsearch_Some_None : forall (A1 A2:Set) (R : A1 -> A2 -> Prop) m1 m2 k a,
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

Lemma GenForall2_bsearch_None_Some : forall (A1 A2:Set) (R : A1 -> A2 -> Prop) m1 m2 k a,
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

Lemma fold_right_and_Forall : forall (A:Set) (p : A -> Prop) l,
    fold_right (fun a accum => p a /\ accum) True l ->
    Forall p l.
Proof.
  induction l; intros; simpl in *.
  auto.
  econstructor; tauto.
Qed.

Lemma Forall_fold_right_and : forall (A:Set) (p : A -> Prop) p0 l,
    p0 /\ Forall p l -> fold_right (fun a accum => p a /\ accum) p0 l.
Proof.
  induction l; simpl; intros.
  tauto.
  destruct H.
  inversion H0. subst.
  tauto.
Qed.

Lemma fold_map_app : forall A t (l : list A),
    foldr_map (fun (a : A) accum => a :: accum) l t
    = foldr_map (fun a accum => a :: accum) [] t ++ l.
Proof.
  induction t0; simpl; intros.
  destruct a.
  rewrite IHt0_2.
  rewrite IHt0_1.
  setoid_rewrite IHt0_1 at 2.
  rewrite <- app_assoc.
  simpl.
  auto.
  auto.
Qed.

Tactic Notation "eapply" "->" constr(lemma) "in" hyp(J) :=
  bapply lemma ltac:(fun H => destruct H as [H _]; eapply H in J).

Lemma Forall_appl : forall A l1 l2 (P : A -> Prop),
    Forall P (l1 ++ l2) -> Forall P l1.
Proof.
  intros.
  apply <- Forall_forall.
  intros.
  eapply -> Forall_forall in H; eauto.
  apply in_or_app. auto.
Qed.

Lemma Forall_appr : forall A l1 l2 (P : A -> Prop),
    Forall P (l1 ++ l2) -> Forall P l2.
Proof.
  intros.
  apply <- Forall_forall.
  intros.
  eapply -> Forall_forall in H; eauto.
  apply in_or_app. auto.
Qed.

Lemma GenForall2_Forall2_map : forall (A1 A2:Set) (R : A1 -> A2 -> Prop) m1 m2,
    GenForall2 R m1 m2 <-> Forall2_map R m1 m2.
Proof.
  intros.
  split.
  intros.
  destruct H.
  destruct H.
  replace (fun '(a1, a2) (p : Prop) => R a1 a2 /\ p) with
  (fun a p => prod_curry R a /\ p) in H0.
  all:swap 1 2.
  unfold prod_curry.
  extensionality a0.
  extensionality p.
  destruct a0.
  auto.
  apply fold_right_and_Forall in H0.
  revert m2 x H H0.
  induction m1; intros.
  destruct m2; simpl in *.
  destruct a.
  destruct p.
  destruct (Nat.eq_dec n n0); [|congruence].
  subst.
  destruct (zip_map m1_1 m2_1) eqn:?; [|congruence].
  destruct (zip_map m1_2 m2_2) eqn:?; [|congruence].
  inversion H.
  subst.
  econstructor.
  unfold from_map_to_list in H0.
  simpl in H0.
  eapply -> Forall_forall in H0.
  change (prod_curry R (a,a0)).
  apply H0.
  assert (In (a,a0) ((a, a0)
        :: foldr_map
        (fun (a1 : A1 * A2) (accum : list (A1 * A2)) => a1 :: accum) [] t1))
    by intuition.
  revert H1.
  generalize ((a,a0) :: foldr_map (fun  (a1 : A1 * A2) (accum : list (A1 * A2)) => a1 :: accum) [] t1).
  clear H H0 Heqo.
  induction t0; simpl; intros.
  destruct a1.
  apply IHt0_1; simpl; auto.
  auto.
  eapply IHm1_1.
  eauto.
  unfold from_map_to_list in *.
  simpl in H0.
  rewrite fold_map_app in H0.
  apply Forall_appl in H0.
  auto.
  eapply IHm1_2.
  eauto.
  unfold from_map_to_list in H0.
  simpl in H0.
  rewrite fold_map_app in H0.
  apply Forall_appr in H0.
  inversion H0. subst.
  apply H4.
  destruct a. congruence.
  destruct m2.
  simpl in H.
  congruence.
  econstructor.
  simpl in *.
  revert m2.
  unfold GenForall2.
  induction m1; simpl; intros.
  inversion H. subst.
  apply IHm1_1 in H5.
  apply IHm1_2 in H6.
  destruct H5.
  destruct H0.
  destruct H6.
  destruct H2.
  exists (Node (k,(a1,a2)) x x0).
  split.
  simpl.
  destruct (Nat.eq_dec k k); [|congruence].
  unfold zip in *.
  simpl in *.
  rewrite H0.
  rewrite H2.
  auto.
  simpl.
  unfold from_map_to_list.
  simpl.
  rewrite fold_map_app.
  rewrite fold_right_app.
  simpl.
  unfold to_list in *.
  simpl in *.
  unfold from_map_to_list in *.
  replace (fun '(a1,a2) p => R a1 a2 /\ p) with
  (fun (a : A1 * A2) p => (let (a1,a2) := a in R a1 a2) /\ p) in *.
  apply fold_right_and_Forall in H1.
  apply Forall_fold_right_and.
  repeat split; auto.
  extensionality a.
  destruct a.
  auto.
  exists (Leaf _).
  inversion H.
  split; simpl; auto.
Qed.

Lemma GenForall2_bsearch_Some : forall (A1 A2:Set) (R : A1 -> A2 -> Prop) m1 m2 k a1 a2,
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
*)

Lemma GenForall2_bsearch_Some_equiv_coro :
  forall (A B : Set) (IA : Inhabit A) (IB : Inhabit B) (state : Set)
         (step : step_type (const_yield A) (const_yield B) unit state)
         x1 x2 n a1 a2,
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

Hint Resolve GenForall2_bsearch_Some_equiv_coro : foldable.


Definition coro_map_loop fuel :=
  let_coro c := ex_coroutine 0 in
        nat_rect_nondep
          (fun _ => Return (Some tt))
          (fun _ rec m' =>
             key <- getStr;
               match bsearch key m' : option (@coro_type nat nat _ _) with
               | Some c =>
                 n <- getN;
                   r <- resume c $ n;
                   putN r;
                   rec (replace_map key c m')
               | None => rec m'
               end)
          fuel (Node ("key",c) (Leaf _) (Leaf _)).

Hint Constructors ex equiv'.
Hint Unfold equiv_coro'.

(*
Lemma coro_map_loop_eq : forall fuel,
    coro_map_loop fuel =
    ltac:(let x := (eval red in (coro_map_loop fuel)) in
          let x' := coro_to_state x in exact x').
Proof.
  intros.
  unfold coro_map_loop, pipe.
  repeat mid_eq_core.
Qed.
 *)

Lemma coro_map_loop_derive : forall fuel,
    { state & { step & { init | @equiv _ _ _  _ state step init (coro_map_loop fuel) }}}.
Proof.
  intros.
  do 3 eexists.
  unshelve derive (tt,fuel); exact inhabitant.
Defined.


Definition echo name s :
  t (const_yield String.string) (const_yield String.string) unit :=
  s' <- yield (String.append (String.append s " from ") name);
    _ <- yield (String.append (String.append s' " from ") name);
    Return tt.

Lemma echo_derive :
  { state & { step & forall name, { init | @equiv_coro' _ _ _ _ _ state step init (echo name) }}}.
Proof.
  do 3 eexists.
  unshelve derive_coro (tt,name); exact inhabitant.
Defined.

Definition echo_step := projT1 (projT2 echo_derive).

Definition echo_equiv n : equiv_coro' echo_step _ (echo n) :=
  proj2_sig (projT2 (projT2 echo_derive) n).

Definition echo_equiv' n
  : equiv_coro' ltac:(let x := eval simpl in (projT1 (projT2 echo_derive)) in exact x) ltac:(let x := eval simpl in (proj1_sig (projT2 (projT2 echo_derive) n)) in exact x) (echo n) :=
  echo_equiv n.

Hint Resolve echo_equiv echo_equiv' : equivc equivc'.
Hint Resolve echo_equiv : equivc'.

Definition sendHello fuel :=
  let_coro c0 := echo "c0" in
  let_coro c1 := echo "c1" in
  nat_rect_nondep
    (fun _ => Return (Some tt))
    (fun _ rec m =>
       key <- getStr;
         match bsearch key m : option (@coro_type String.string String.string _ _) with
         | Some c =>
           r <- resume c $ "hello";
             putStr r;
             rec (replace_map key c m)
         | None => rec m
         end)
    fuel (Node ("key0",c0) (Node ("key1",c1) (Leaf _) (Leaf _)) (Leaf _)).

(*
Lemma sendHello_eq : forall fuel,
    sendHello fuel =
    ltac:(let x := (eval red in (sendHello fuel)) in
          let x' := coro_to_state x in exact x').
Proof.
  intros.
  unfold sendHello, pipe.
  repeat mid_eq_core.
Qed.
 *)

Lemma sendHello_derive fuel :
  {state & {step & {init | @equiv _ _ _ _ state step init (sendHello fuel)}}}.
Proof.
  do 3 eexists.
  unshelve derive (tt,fuel); exact inhabitant.
Defined.

