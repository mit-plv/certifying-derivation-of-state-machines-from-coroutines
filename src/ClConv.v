Require String.
Import String.StringSyntax.
Require Import List FunctionalExtensionality Arith.
Require Import StateMachines.Inhabit StateMachines.Foldable.
Import ListNotations.
Open Scope type_scope.
Open Scope string_scope.
Set Implicit Arguments.

Arguments existT {_ _} _ _.

Section Effect.
  Context (eff : Set)(args rets: eff -> Set).

  Inductive t (ret_type : Set) :=
  | Eff : forall (e : eff), args e -> (rets e -> t ret_type) -> t ret_type
  | Return : ret_type -> t ret_type.

  Definition step_type (ret_type state : Set) := state -> forall (e : eff),
      rets e -> (state * option { e : eff & args e }) + ret_type.

  Inductive equiv' (ret_type C state : Set)(step : step_type ret_type state) P:
    state -> t C -> option { e : eff & args e } -> Prop :=
  | Equiv'Eff : forall s e (a : args e) p next op,
      (forall r, equiv' step P (next r) (p r) (op r)) ->
      (forall r, step s e r = inl (next r, op r)) ->
      equiv' step P s (Eff a p) (Some (existT _ a))
  | Equiv'Return : forall s op o,
      P s op o ->
      equiv' step P s (Return o) op.

  Definition equiv ret_type state (step : step_type ret_type state) init p :=
    exists op s, step init = (fun _ _ => inl (s, op)) /\ equiv' (ret_type := ret_type) step (fun s op o => (step s = fun _ _ => inr o) /\ op = None) s p op.

End Effect.

Arguments Return {_ _ _ _ } _.

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

Definition seqE (A B C D ef:Set)(args rets : ef -> Set) (e : t (const_yield A) (const_yield B) D)
  : (A -> (B -> t (const_yield A) (const_yield B) D) ->
     t args rets (option C)) ->
    t args rets (option C) :=
  match e with
  | Return c => fun _ => Return None
  | Eff _ a p => fun cont => cont a p
  end.

Definition coro_type A B C state
           (_ : step_type (const_yield A) (const_yield B) C state):=
  B -> t (const_yield A)(const_yield B) C.


Definition proc_coro (A B C D ef : Set)(args rets : ef -> Set)(state : Set)
           (step : step_type (const_yield A)(const_yield B) D state)
           (c : coro_type step) (x : B)
  : (A -> coro_type step -> t args rets (option C)) ->
    t args rets (option C) :=
  seqE (c x).

Fixpoint bind (T S eff : Set)(args rets : eff -> Set)
         (x : t args rets T)(p : T -> t args rets S) :=
  match x with
  | Return v => p v
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
  Return (S n).
  
Definition seqE' A C R (ef:Set) (args rets:ef -> Set) state
           (x : (state * option { e : yield_effect & A }) + R)
           (f : state -> A -> t args rets C)
           (f0 : t args rets C) :=
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

Inductive ternary (A B C : Set) :=
| tnr1 : A -> ternary A B C
| tnr2 : B -> ternary A B C
| tnr3 : C -> ternary A B C.

Arguments tnr1 {_ _ _} _.
Arguments tnr2 {_ _ _} _.
Arguments tnr3 {_ _ _} _.

Definition ternary_merge (A B C D : Set) f g h (x : ternary A B C) : D :=
  match x with
  | tnr1 a => f a
  | tnr2 b => g b
  | tnr3 c => h c
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
  lazymatch goal with
    |- ?L = ?X =>
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
  repeat lazymatch goal with
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
           try apply eq_refl
         end.

Ltac dest_sum :=
  let e := open_constr:(_|||_) in
  lazymatch goal with
  | |- ?g (inl _) _ _ = ?t =>
    unify g e
  | |- ?g (inr _) _ _ = _ =>
    unify g e
  | |- ?g (inl _) = ?t =>
    unify g e
  | |- ?g (inr _) = _ =>
    unify g e
  end.

Ltac dest_ternary :=
  let e := open_constr:(ternary_merge _ _ _) in
  lazymatch goal with
  | |- ?g (tnr1 _) _ _ = _ => unify g e
  | |- ?g (tnr2 _) _ _ = _ => unify g e
  | |- ?g (tnr3 _) _ _ = _ => unify g e
  | |- ?g (tnr1 _) = _ => unify g e
  | |- ?g (tnr2 _) = _ => unify g e
  | |- ?g (tnr3 _) = _ => unify g e
  end.

Definition dmmy (A:Set)(_:A) := True.

Ltac free_var body vars :=
  lazymatch goal with
    _ : dmmy ?env |- _ =>
    let rec aux vars :=
        lazymatch vars with
        | env => env
        | (?rest,?a) =>
          let r := aux rest in
          lazymatch body with
          | context [a] => constr:((r,a))
          | _ => r
          end
        | _ => tt
        end
    in
    aux vars
  | _ =>
    let rec aux vars :=
        lazymatch vars with
        | (?rest,?a) =>
          let r := aux rest in
          lazymatch body with
          | context [a] => constr:((r,a))
          | _ => r
          end
        | _ => tt
        end
    in
    aux vars
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
    Return tt.

Ltac st_absorb_args' :=
  cbv beta;
  lazymatch goal with
    |- equiv' _ _ ?st' _ _ =>
    lazymatch st' with
    | _ (_,_) _ =>
      let u := open_constr:(_) in
      replace st' with u; [|symmetry]
    | ?f _ _ =>
      let u := open_constr:(fun _ _ => _) in
      unify f u
    | ?f _ =>
      let u := open_constr:(fun _ => _) in
      unify f u
    | _ => idtac
    end
  end.

Ltac st_absorb_args :=
  lazymatch goal with
    |- equiv' _ _ ?st _ _ =>
    lazymatch st with
    | ?f _ _ _ =>
      let u := open_constr:(fun _ _ _ => _) in
      unify f u
    | ?f ?a _ =>
      st_absorb_args'
    | ?f _ =>
      let u := open_constr:(fun _ => _) in
      unify f u
    | _ => idtac
    end
  end.

Ltac op_absorb_args' :=
  cbv beta;
  lazymatch goal with
    |- equiv' _ _ _ _ ?op =>
    lazymatch op with
    | _ (_,_) _ =>
      let u := open_constr:(_) in
      replace op with u; [|symmetry]
    | ?f _ _ =>
      let u := open_constr:(fun _ _ => _) in
      unify f u
    | ?f _ =>
      let u := open_constr:(fun _ => _) in
      unify f u
    | _ => idtac
    end
  end.

Ltac op_absorb_args :=
  lazymatch goal with
    |- equiv' _ _ _ _ ?op =>
    lazymatch op with
    | ?f _ _ _ =>
      let u := open_constr:(fun _ _ _ => _) in
      unify f u
    | _ _ _ =>
      op_absorb_args'
    | ?f _ =>
      let u := open_constr:(fun _ => _) in
      unify f u
    | _ => idtac
    end
  end.

Ltac st_op_to_ev :=
  st_absorb_args; [op_absorb_args; [cbv beta|..]|..].
(*
Ltac st_op_to_ev :=
  lazymatch goal with
    |- equiv' ?step _ ?st ?prog ?op =>
    lazymatch st with
    | ?f _ _ =>
      let u := open_constr:(fun r c => _) in
      unify f u
    | ?f _ =>
      let u := open_constr:(fun r => _) in
      unify f u
    | _ => idtac
    end;
    lazymatch op with
    | ?g _ _ =>
      let u := open_constr:(fun r c => _) in
      unify g u
    | ?g _ =>
      let u := open_constr:(fun r => _) in
      unify g u
    | _ => idtac
    end;
    cbv beta
  end.
*)

Lemma derive_bind :
  forall state C D E (eff : Set)(args rets : eff -> Set) P
         (step : step_type args rets C state) c p st op st' op' ,
    (@equiv' _ args rets C E state step (fun st'' op'' o => st'' = st' o /\ op'' = op' o) st c op) ->
    (forall r, equiv' step P (st' r) (p r) (op' r)) ->
    @equiv' _ args rets C D state step P st (bind c p) op.
Proof.
  intros.
  induction H; simpl.
  econstructor.
  intros.
  apply H1.
  intros.
  apply H2.
  destruct H.
  subst.
  auto.
Qed.

(*
Lemma derive_nat_rect : forall state A C D (eff : Set)(args rets : eff -> Set) N (a0:A) f f0 st0 stS op0 opS step g,
    (forall a, equiv' step g (st0 a) (f a a) (op0 a)) ->
    (forall N0,
        (forall a, equiv' step g
                          ((fix aux N0 := match N0 with O => st0 a | S N0' => stS a N0' end) N0)
                          (nat_rect_nondep (f a) (f0 a) N0 a)
                          ((fix aux N0 := match N0 with O => op0 a | S N0' => opS a N0' end) N0)) ->
        (forall a, equiv' step g (stS a N0)
                          (f0 a N0
                              (nat_rect_nondep
                                    (f a) (f0 a)
                                    N0) a) (opS a N0))) ->
    @equiv' _ args rets C D state step g
            ((fix aux n := match n with O => st0 a0 | S n0 => stS a0 n0 end) N)
            (nat_rect_nondep (f a0) (f0 a0) N a0)
            ((fix aux n := match n with O => op0 a0 | S n0 => opS a0 n0 end) N).
Proof.
  intros.
  revert a0.
  induction N; intros; simpl; auto.
Qed.
*)

Lemma derive_nat_rect : forall state A C D (eff : Set)(args rets : eff -> Set) N (a0:A) f f0 st0 stS op0 opS step g,
    (forall a, equiv' step g (st0 a) (f a a) (op0 a)) ->
    (forall N0,
        (forall a, equiv' step g (match N0 with O => st0 a | S N0' => stS a N0' end) (nat_rect_nondep (f a) (f0 a) N0 a) (match N0 with O => op0 a | S N0' => opS a N0' end)) ->
        (forall a, equiv' step g (stS a N0)
                          (f0 a N0
                              (nat_rect_nondep
                                    (f a) (f0 a)
                                    N0) a) (opS a N0))) ->
    @equiv' _ args rets C D state step g (match N with O => st0 a0 | S N0 => stS a0 N0 end) (nat_rect_nondep (f a0) (f0 a0) N a0) (match N with O => op0 a0 | S N0 => opS a0 N0 end).
Proof.
  intros.
  revert a0.
  induction N; intros; simpl; auto.
Qed.

Lemma derive_list_rec : forall state A B C D (eff : Set)(args rets : eff -> Set)(l : list B)(a0:A) f f0 st0 stS op0 opS step P,
    (forall a, equiv' step P (st0 a) (f a a) (op0 a)) ->
    (forall b0 l0,
        (forall a,
            equiv' step P
                   (match l0 with [] => st0 a | b::l' => stS a b l' end)
                   (list_rec_nondep (f a) (f0 a) l0 a)
                   (match l0 with [] => op0 a | b::l' => opS a b l' end)) ->
        (forall a, equiv' step P (stS a b0 l0)
                          (f0 a b0 l0
                              (list_rec_nondep
                                 (f a) (f0 a)
                                 l0) a) (opS a b0 l0))) ->
    @equiv' _ args rets C D state step P
            (match l with [] => st0 a0 | b::l' => stS a0 b l' end)
            (list_rec_nondep (f a0) (f0 a0) l a0)
            (match l with [] => op0 a0 | b::l' => opS a0 b l' end).
Proof.
  intros.
  revert a0.
  induction l; intros; simpl; auto.
Qed.

Definition option_branch A B (f:A -> B) f0 o :=
  match o with
  | Some a => f a
  | None => f0
  end.

Lemma derive_opt : forall eff args rets A C D state (x : option A) sta st fa f opa op step P,
    (forall a, equiv' step P (sta a) (fa a) (opa a)) ->
    equiv' step P st f op ->
    @equiv' eff args rets C D state step P
            (option_branch sta st x)
            (match x with Some a => fa a | None => f end)
            (option_branch opa op x).
Proof.
  intros.
  unfold option_branch.
  destruct x; auto.
Qed.


Lemma derive_opt' : forall eff args rets A C D state (x : option A) sta st fa f opa op step P,
    (forall a, equiv' step P (sta a) (fa a) (opa a)) ->
    equiv' step P st f op ->
    @equiv' eff args rets C D state step P
            (option_branch sta st x)
            (option_branch fa f x)
            (option_branch opa op x).
Proof.
  intros.
  unfold option_branch.
  destruct x; auto.
Qed.

Lemma derive_bool : forall eff args rets C D state (b:bool) stt stf ft ff opt opf step P,
    equiv' step P stt ft opt ->
    equiv' step P stf ff opf ->
    @equiv' eff args rets C D state step P (if b then stt else stf)
            (if b then ft else ff) (if b then opt else opf).
Proof.
  intros.
  destruct b; auto.
Qed.

Lemma derive_sum : forall eff args rets A B C D state (x : A + B) fa fb sta stb opa opb step P,
    (forall a, equiv' step P (sta a) (fa a) (opa a)) ->
    (forall b, equiv' step P (stb b) (fb b) (opb b)) ->
    @equiv' eff args rets C D state step P
            (match x with
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

Lemma derive_sum' : forall eff args rets (A B C D:Set) state (x : A + B) fa fb sta stb opa opb step P,
    (forall a, equiv' step P (sta a) (fa a) (opa a)) ->
    (forall b, equiv' step P (stb b) (fb b) (opb b)) ->
    @equiv' eff args rets C D state step P (match x with
                                        | inl a => sta a
                                        | inr b => stb b
                                        end)
            (sum_merge fa fb x)
            (match x with
             | inl a => opa a
             | inr b => opb b
             end).
Proof.
  intros.  unfold sum_merge.
  destruct x; auto.
Qed.

Lemma derive_prod : forall eff args rets A B C D state (x : A * B) f st op step P,
    (forall a b, equiv' step P (st a b) (f a b) (op a b)) ->
    @equiv' eff args rets C D state step P
            match x with
            | (a,b) => st a b
            end
            match x with
            | (a,b) => f a b
            end
            match x with
            | (a,b) => op a b
            end.
Proof.
  intros.
  destruct x.
  auto.
Qed.

Lemma derive_seqE' :
  forall A C D R (eff : Set)(args rets : eff -> Set)state state'
         (x : (state' * option { _ : yield_effect & A }) + R)
         f f0 g g0 h h0 step P,
    (forall s v, equiv' step P (g s v) (f s v) (h s v)) ->
    equiv' step P g0 f0 h0 ->
    @equiv' _ args rets C D state step P
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

Definition step_state (A B C R eff : Set)(args rets : eff -> Set)(state : Set)
           (step : step_type (const_yield A)(const_yield B) R state) st x g :=
  seqE' (step st yield x) (fun s v => g v s) (Return (args:=args) (rets:=rets) (@None C)).

Lemma equal_f_dep : forall A (T : A -> Set) B (f g : forall a, T a -> B) a0,
    f = g -> f a0 = g a0.
Proof.
  intros.
  rewrite H.
  auto.
Qed.

Ltac next_ptr :=
  lazymatch goal with
    |- @equiv' _ _ _ _ _ ?st _ _ _ _ _ =>
    let rec aux state accum :=
        lazymatch state with
        | ?A + (?B + ?T) =>
          aux T open_constr:(fun x => accum (@inr A _ (@inr B _ x)))
        | ?A + ?B => open_constr:(fun x => accum (@inr A B x))
        | ?A => open_constr:(fun x:A => accum x)
        end
    in
    aux st open_constr:(fun x => x)
  end.

Ltac next_ptr' :=
  lazymatch goal with
    |- @equiv' _ _ _ _ _ ?st _ _ _ _ _ =>
    let rec aux state accum :=
        lazymatch state with
        | ternary ?A ?B (ternary ?C1 ?C2 ?C3) =>
          lazymatch C2 with
          | unit =>
            aux (ternary C1 C2 C3) open_constr:(fun x => accum (@tnr3 A B _ x))
          | _ * _ =>
            aux (ternary C1 C2 C3) open_constr:(fun x => accum (@tnr3 A B _ x))
          | _ =>
            open_constr:((true, fun x => accum (@tnr3 A B _ (@tnr2 C1 C2 C3 x))))
          end
        | ternary ?A ?B ?C =>
          open_constr:((false,fun x => accum (@tnr3 A B C x)))
        | _ => open_constr:((true,accum))
        end
    in
    aux st open_constr:(fun x => x)
  end.

Definition my_pair A B (a : A)(b : B) := (a,b).
Opaque my_pair.

(*
Ltac take_head p x H :=
  repeat match x with
         | context ctx [my_pair ?e ?a] =>
           match e with
           | my_pair _ _ => fail 1
           | _ =>
             let dummy := open_constr:(_) in
             let x' := context ctx [dummy] in
             let r := open_constr:((a,x')) in
             unify p r;
             set (H := True)
           end
         end.
*)

Ltac take_head q :=
  let rec aux q accum :=
      lazymatch q with
      | my_pair (my_pair tt ?a) ?b =>
        let q' := (eval cbv beta in (accum (my_pair tt b))) in
        open_constr:((a, q'))
      | my_pair tt ?a =>
        let q' := (eval cbv beta in (accum tt)) in
        open_constr:((a,q'))
      | my_pair ?a ?b =>
        aux a open_constr:(fun v => my_pair v b)
      end
  in
  aux q open_constr:(fun x => x).

Ltac next_ptr'' :=
  lazymatch goal with
    |- @equiv' _ _ _ _ _ ?st _ _ _ _ _ =>
    let rec aux queue :=
        let r := take_head queue in
        lazymatch r with
        | ((?state,?accum),?queue') =>
          lazymatch state with
          | ternary ?A ?B ?C =>
            aux open_constr:(my_pair (my_pair queue' (B, (fun x => accum (@tnr2 A B C x))))
                         (C, (fun x => accum (@tnr3 A B C x))))
          | ?A => open_constr:(accum)
          end
        end
    in
    aux open_constr:(my_pair tt (st, fun x => x))
  end.

Ltac next_state :=
  lazymatch goal with
    |- @equiv' _ _ _ _ _ ?st _ _ _ _ _ =>
    let rec aux state stateF ptr stepF :=
        lazymatch state with
        | ?A + ?B =>
          aux B open_constr:(fun T:Set => stateF (A + T))
              open_constr:(fun x => ptr (@inr A B x))
              open_constr:(fun f => stepF (_ ||| f))
        | ?A => open_constr:((stateF, ptr, stepF))
        end
    in
    aux st open_constr:(fun x => x) open_constr:(fun x => x) open_constr:(fun x => x)
  end.

Ltac next_state' :=
  lazymatch goal with
    |- @equiv' _ _ _ _ _ ?st _ _ _ _ _ =>
    let rec aux state stateF ptr stepF :=
        lazymatch state with
        | ternary ?A ?B ?C =>
          aux C open_constr:(fun T:Set => stateF (ternary A B T))
                open_constr:(fun x => ptr (@tnr3 A B C x))
                open_constr:(fun f => stepF (ternary_merge _ _ f))
        | _ => open_constr:((stateF, ptr, stepF))
        end
    in
    aux st open_constr:(fun x => x) open_constr:(fun x => x) open_constr:(fun x => x)
  end.

Ltac next_state'' stateF0 ptr0 stepF0 :=
  lazymatch goal with
    |- @equiv' _ _ _ _ _ ?st _ _ _ _ _ =>
    let rec aux queue :=
        let r := open_constr:(_) in
        let H := fresh in
        take_head r queue H;
        clear H;
        lazymatch r with
        | ((?state,?stateF,?ptr,?stepF),?queue') =>
          lazymatch state with
          | ternary ?A ?B ?C =>
            aux open_constr:(my_pair
                               (my_pair queue' (B, (fun T:Set => stateF (ternary A T C)), (fun x => ptr (@tnr2 A B C x)), (fun f => stepF (ternary_merge _ f _))))
                               (C, (fun T:Set => stateF (ternary A B T)), (fun x => ptr (@tnr3 A B C x)), (fun f => stepF (ternary_merge _ _ f))))
          | ?A =>
            unify stateF0 stateF;
            unify ptr0 ptr;
            unify stepF0 stepF
          end
        end
    in
    aux open_constr:(my_pair tt (st, (fun x => x), (fun x => x), (fun x => x)))
  end.
    

Definition lift_yield R A B (e:yield_effect)(a : R -> A + option B)(e0 : yield_effect)
  : R -> A + option B :=
  a.

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

Class is_eff eff :=
  { args : eff -> Set;
    rets : eff -> Set;
    lift_eff : forall (A B : Type) (e : eff),
        (rets e -> A + option B) ->
        forall e0 : eff, rets e0 -> A + option B }.

Instance effect_is_eff : is_eff effect :=
  { args := args_effect;
    rets := rets_effect;
    lift_eff := lift_effect }.

Definition const A B (b:B) := fun _:A => b.

Ltac dest_step :=
  lazymatch goal with
    |- @eq (?T1 + ?T2) (?g _ ?ef ?r) _ =>
    pattern_rhs r;
    apply equal_f;
      lazymatch goal with
        |- ?lhs = ?rhs =>
        lazymatch ef with
        | yield =>
          change (lhs = const rhs yield)
          || enough (lhs = const rhs yield) by (unfold const; assumption)
        | _ => change rhs with (lift_eff ef rhs ef)
        end
      end;
      (apply equal_f_dep || apply equal_f);
      try unfold const;
      cbv beta iota;
      repeat (dest_sum; unfold sum_merge; cbv beta iota);
      unify_fun
  | |- _ ?r = _ =>
    lazymatch goal with
      |- ?lhs = _ =>
      repeat (dest_sum; unfold sum_merge; cbv beta iota); unify_fun
    end
  end.

Ltac dest_step' :=
  lazymatch goal with
    |- (?g _ ?ef ?r) = _ =>
    pattern_rhs r;
    apply equal_f;
    lazymatch goal with
      |- ?lhs = ?rhs =>
      lazymatch ef with
      | yield =>
        change (lhs = const rhs yield)
        || enough (lhs = const rhs yield) by (unfold const; assumption)
      | _ => change rhs with (lift_eff ef rhs ef)
      end
    end;
    (apply equal_f_dep || apply equal_f);
    try unfold const;
    cbv beta iota;
    repeat (dest_ternary; unfold ternary_merge; cbv beta iota);
    unify_fun
  | |- _ _ = _ =>
    lazymatch goal with
      |- _ = _ =>
     repeat (dest_ternary; unfold ternary_merge; cbv beta iota); unify_fun
    end
 end.

Lemma bind_if : forall C D (b:bool)(p q : t args_effect rets_effect C)(r : C -> t args_effect rets_effect D),
  bind (if b then p else q) r
  = if b then bind p r else bind q r.
Proof.
  intros.
  destruct b; auto.
Qed.

Definition Def {A B : Set} (a : A)(f : A -> B) := f a.

Ltac derive_core (*ptr*) env :=
  st_op_to_ev;[
    (solve [repeat match goal with
                   | H : ?p |- _ =>
                     match type of p with
                     | Prop =>
                       match p with
                       | forall _, _ => eapply (H _)
                       | equiv' _ _ _ _ _ => apply H
                       end
                     end
                   end])
    ||
    lazymatch goal with
      |- equiv' ?step ?P _ ?prog _ =>
    lazymatch prog with
    | Def ?c ?p =>
      lazymatch c with
      | (fun _ => _) =>
        eassert (forall a, equiv' step P _ (c a) _);
        [ intro;
          derive_core (*ptr*) env
        | unfold Def at 1;
          (*let ptr := next_ptr open_constr:(fun _x => _x) in*)
          derive_core (*ptr*) env
        ]
      | _ =>
        eassert (equiv' step P _ c _);
        [ derive_core (*ptr*) env
        | unfold Def at 1;
          (*let ptr := next_ptr open_constr:(fun _x => _x) in*)
          derive_core (*ptr*) env
        ]
      end
    | @Eff _ ?args ?rets ?C ?e _ _ =>
      let fv := free_var prog env in
      let ptr := next_ptr in
      eapply (Equiv'Eff (ptr (inl fv)) e);
      [ let H := fresh in
        intro H;
        derive_core (fv, H)
      | intros; dest_step
      ]
    | Return _ =>
      idtac
    | bind ?c _ =>
      let fv := free_var prog env in
      eapply (derive_bind _ (fun _ => _) (fun _ => _));
      [ assert (dmmy fv) by (unfold dmmy; exact I);
        (*let ptr := next_ptr open_constr:(fun _x => _x) in*)
        derive_core (*ptr*) fv
      | let r := fresh in
        intro r;
        cbv beta;
        (*let ptr := next_ptr open_constr:(fun _x => _x) in*)
        derive_core (*ptr*) (fv,r)
      ]
    | seqE' _ _ _ =>
      eapply (derive_seqE' _ (fun s v => _) (fun s v => _) (fun s v => _));
      [ let s := fresh in
        let v := fresh in
        intros s v;
        derive_core (*ptr*) (env,s,v)
      | (*let ptr := next_ptr open_constr:(fun _x => _x) in*)
        derive_core (*ptr*) env ]
    | (match ?x with inl _ => _ | inr _ => _ end) =>
      eapply (derive_sum _ _ _ (fun a => _) (fun b => _) (fun a => _) (fun b => _));
      [ let a := fresh in
        intro a;
        cbv beta;
        (*let ptr := next_ptr open_constr:(fun _x => _x) in*)
        derive_core (*ptr*) (env,a)
      | let b := fresh in
        intro b;
        cbv beta;
        (*let ptr := next_ptr open_constr:(fun _x => _x) in*)
        derive_core (*ptr*) (env,b)
      ]
    | (sum_merge _ _ ?x) =>
      eapply (derive_sum' _ _ _ (fun _ => _) (fun _ => _) (fun _ => _) (fun _ => _));
      [ let a := fresh in
        intro a;
        cbv beta;
        (*let ptr := next_ptr open_constr:(fun _x => _x) in*)
        derive_core (*ptr*) (env,a)
      | let b := fresh in
        intro b;
        cbv beta;
        (*let ptr := next_ptr open_constr:(fun _x => _x) in*)
        derive_core (*ptr*) (env,b)
      ]
    | (match ?x with Some _ => _ | None => _ end) =>
      eapply (derive_opt _ (fun _ => _) (fun _ => _) (fun _ => _));
      [ let _a := fresh in
        intro _a;
        cbv beta;
        (*let ptr := next_ptr open_constr:(fun _x => _x) in*)
        derive_core (*ptr*) (env,_a)
      | cbv beta;
        (*let ptr := next_ptr open_constr:(fun _x => _x) in*)
        derive_core (*ptr*) env
      ]
    | option_branch _ _ ?x =>
      eapply (derive_opt' _ (fun _ => _) (fun _ => _) (fun _ => _));
      [ let _a := fresh in
        intro _a;
        cbv beta;
        (*let ptr := next_ptr open_constr:(fun _x => _x) in*)
        derive_core (*ptr*) (env,_a)
      | cbv beta;
        (*let ptr := next_ptr open_constr:(fun _x => _x) in*)
        derive_core (*ptr*) env
      ]
    | (match ?b with true => _ | false => _ end) =>
      eapply derive_bool;
      [ (*let ptr := next_ptr open_constr:(fun _x => _x) in*)
        derive_core (*ptr*) env
      | (*let ptr := next_ptr open_constr:(fun _x => _x) in*)
        derive_core (*ptr*) env
      ]
    | (match ?x with (_,_) => _ end) =>
      eapply (derive_prod _ (fun _ _ => _) (fun _ => _) (fun _ => _));
      let _a := fresh in
      let _b := fresh in
      intros _a _b;
      derive_core (*ptr*) (env,_a,_b)
    | nat_rect_nondep _ _ _ _ =>
      (eapply (derive_nat_rect _ _ (fun a b => _) (fun a => _) (fun a => _));
       [ let a := fresh in
         intro a;
         cbv beta;
         (*let ptr := next_ptr open_constr:(fun _x => _x) in*)
         derive_core (*ptr*) (env,a)
       | let n := fresh in
         let H := fresh in
         let a := fresh in
         intros n H a;
         cbv beta;
         (*let ptr := next_ptr open_constr:(fun _x => _x) in*)
         derive_core (*ptr*) (env,n,a)
      ])
    | list_rec_nondep _ _ _ _ =>
      (solve [repeat match goal with
                   | H : ?p |- _ => apply H
                   end])
      ||
      (eapply (derive_list_rec _ _ (fun _ _ => _) (fun _ => _) (fun _ => _));
       [ let a := fresh in
         intro a;
         cbv beta;
         (*let ptr := next_ptr open_constr:(fun _x => _x) in*)
         derive_core (*ptr*) (env,a)
       | let b := fresh in
         let l := fresh in
         let H := fresh in
         let a := fresh in
         intros b l H a;
         cbv beta;
         (*let ptr := next_ptr open_constr:(fun _x => _x) in*)
         derive_core (*ptr*) (env,b,l,a)
      ])
    | _ => let prog' := (eval red in prog) in
           change prog with prog';
           derive_core (*ptr*) env
    end
    end|unify_fun..].

Definition pipe A B (a : A)(f : A -> B) := f a.

Instance coro_type_inhabitant (A B C:Set) `{IC : Inhabit C} state step :
  Inhabit (@coro_type A B C state step) :=
  { inhabitant := fun _ => Return inhabitant }.

Instance t_inhabitant e a r (c:Set) `{IC : Inhabit c} : Inhabit (@t e a r c) :=
  { inhabitant := Return inhabitant }.

Definition seq_abs A B (eff : Set) (args rets : eff -> Set) R state
           (step : step_type (const_yield A)(const_yield B) R state) (x:B) C (_:C) (g : A -> C -> t args rets R ) := t_inhabitant.


Opaque dummy.

Definition equiv_coro (A B C :Set) `{IA : Inhabit A} `{IB : Inhabit B} state
           (step : step_type _ _ C state)
           st
           (coro : B -> t (const_yield A) (const_yield B) C) :=
  exists op, equiv' step (fun s op o => (step s = fun  _ _ => inr o) /\ op = None) st (r <- yield inhabitant; coro r) op.

Ltac get_init c :=
  lazymatch type of c with
  | ?B -> t (const_yield ?A) (const_yield _) ?C =>
    let init := open_constr:(_) in
    let step := open_constr:(_) in
  let _ := constr:(ltac:(auto with equivc) : @equiv_coro A B C _ _ _ step init c) in
  init
  end.

Ltac opt_match_fun expr :=
  lazymatch expr with
  | (match ?o with Some a => _ | None => _ end) =>
    lazymatch (eval pattern o in expr) with
    | ?F _ =>
      eval cbv beta iota in (fun a => F (Some a))
    end
  end.

Ltac sum_match_fun_l expr :=
  lazymatch expr with
  | (match ?o with inl _ => _ | inr _ => _ end) =>
    lazymatch eval pattern o in expr with
    | ?F _ => eval cbv beta iota in (fun a => F (inl a))
    end
  end.

Ltac sum_match_fun_r expr :=
  lazymatch expr with
  | (match ?o with inl _ => _ | inr _ => _ end) =>
    lazymatch eval pattern o in expr with
    | ?F _ => eval cbv beta iota in (fun a => F (inr a))
    end
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
  | @Eff ?eff ?args ?rets ?C ?e ?a ?f =>
    let x := (eval cbv beta in (f (dummy _ _ i))) in
    let d := to_dummy (S i) x in
    lazymatch type of f with
    | ?T -> _ =>
      lazymatch (eval pattern (dummy _ T i) in d) with
      | ?g _ =>
        constr:((@Eff eff args rets C e a, g))
      end
    end
  | @proc_coro ?A ?B ?C ?D ?eff ?args ?rets ?state ?step ?c ?z ?f =>
    let x := (eval cbv beta in (f (dummy _ _ i) (dummy _ _ (S i)))) in
    lazymatch f with
    | context [proc_coro] =>
      let d := to_dummy (S (S i)) x in
      lazymatch type of f with
      | _ -> ?T -> _ =>
        lazymatch (eval pattern (dummy _ A i), (dummy _ T (S i)) in d) with
        | ?g _ _ =>
          constr:((@seq_abs A B eff args rets D state step z (coro_type step) c, g))
        end
      end
    | _ =>
      constr:((@seq_abs A B eff args rets D state step z (coro_type step) c, f))
    end
  | @bind ?T ?T' ?eff ?args ?rets ?p ?f =>
    let x :=  (eval cbv beta in (f (dummy _ _ i))) in
    let d := to_dummy (S i) x in
    let d' := to_dummy i p in
    lazymatch (eval pattern (dummy _ T i) in d) with
    | ?g _ =>
      constr:((@bind T T' eff args rets, d', g))
    end
  | (match ?o with inl _ => _ | inr _ => _ end) =>
    let fl := sum_match_fun_l p in
    let fr := sum_match_fun_r p in
    let ty := type of fl in
    lazymatch ty with
    | ?A -> _ =>
      let ty' := type of fr in
      lazymatch ty' with
      | ?B -> _ =>
        let xl := (eval cbv beta in (fl (dummy _ _ i))) in
        let xr := (eval cbv beta in (fr (dummy _ _ i))) in
        let dl := to_dummy (S i) xl in
        let dr := to_dummy (S i) xr in
        lazymatch (eval pattern (dummy _ A i) in dl) with
        | ?gl _ =>
          lazymatch (eval pattern (dummy _ B i) in dr) with
          | ?gr _ => constr:((@sum_merge A B, gl, gr, o))
          end
        end
      end
    end
  | sum_merge ?fl ?fr ?o =>
    let ty := type of fl in
    lazymatch ty with
    | ?A -> _ =>
      let ty' := type of fr in
      lazymatch ty' with
      | ?B -> _ =>
        let xl := (eval cbv beta in (fl (dummy _ _ i))) in
        let xr := (eval cbv beta in (fr (dummy _ _ i))) in
        let dl := to_dummy (S i) xl in
        let dr := to_dummy (S i) xr in
        lazymatch (eval pattern (dummy _ A i) in dl) with
        | ?gl _ =>
          lazymatch (eval pattern (dummy _ B i) in dr) with
          | ?gr _ => constr:((@sum_merge A B, gl, gr, o))
          end
        end
      end
    end
  | (match ?o with Some _ => _ | None => ?f0 end) =>
    let f := opt_match_fun p in
    let ty := type of o in
    lazymatch ty with
    | option ?A =>
      let B := type of p in
      let x := (eval cbv beta in (f (dummy _ _ i))) in
      let d := to_dummy (S i) x in
      let d0 := to_dummy i f0 in
      lazymatch (eval pattern (dummy _ A i) in d) with
      | ?g _ =>
        constr:((@option_branch A B, g, d0, o))
      end
    | _ =>
      lazymatch (eval simpl in ty) with
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
    end
  | option_branch ?f ?f0 ?o =>
    let ty := type of o in
    lazymatch ty with
    | option ?A =>
      let B := type of p in
      let x := (eval cbv beta in (f (dummy _ _ i))) in
      let d := to_dummy (S i) x in
      let d0 := to_dummy i f0 in
      lazymatch (eval pattern (dummy _ A i) in d) with
      | ?g _ =>
        constr:((@option_branch A B, g, d0, o))
      end
    | _ =>
      lazymatch (eval simpl in ty) with
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
    end
  | (match ?o with (a,b) => _ end) =>
    lazymatch (eval pattern o in p) with
    | ?F _ =>
      let f := (eval cbv beta iota in (fun a b => F (a,b))) in
      let x := (eval cbv beta in (f (dummy _ _ i) (dummy _ _ (S i)))) in
      let d := to_dummy (S (S i)) x in
      lazymatch type of o with
      | ?A * ?B =>
        lazymatch (eval pattern (dummy _ A i), (dummy _ B (S i)) in d) with
        | ?g _ _ => constr:((@prod_curry A B, g, o))
        end
      end
    end
  | @nat_rect_nondep ?A ?f ?f0 ?n ?a =>
    let x := (eval cbv beta in (f0 (dummy _ _ i) (dummy _ _ (S i)) (dummy _ _ (S (S i))))) in
    let y := (eval cbv beta in (f (dummy _ _ i))) in
    let d := to_dummy (S i) y in
    let d0 := to_dummy (S (S (S i))) x in
(*    let T := type of a in*)
    lazymatch A with
      ?T -> _ =>
      lazymatch (eval pattern (dummy _ nat i), (dummy _ A (S i)), (dummy _ T (S (S i))) in d0) with
      | ?g0 _ _ _ =>
        lazymatch (eval pattern (dummy _ T i) in d) with
        | ?g _ =>
          constr:((@nat_rect_nondep A, g, g0, n, a))
        end
      end
    end
  | @list_rec_nondep ?A ?B ?f ?f0 ?l ?a =>
    let x := (eval cbv beta in (f0 (dummy _ _ i) (dummy _ _ (S i)) (dummy _ _ (S (S i))) (dummy _ _ (S (S (S i)))))) in
    let y := (eval cbv beta in (f (dummy _ _ i))) in
    let d := to_dummy (S i) y in
    let d0 := to_dummy (S (S (S (S i)))) x in
    let T := type of a in
    lazymatch (eval pattern (dummy _ A i), (dummy _ (list A) (S i)), (dummy _ B (S (S i))) , (dummy _ T (S (S (S i)))) in d0) with
    | ?g0 _ _ _ _ =>
      lazymatch (eval pattern (dummy _ T i) in d) with
      | ?g _ =>
        constr:((@list_rec_nondep A, B, g, g0, l, a))
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
      let ty' := (eval cbv beta in ty) in
      lazymatch (eval pattern (dummy _ ty' i) in p') with
      | ?p'' _ =>
        constr:(Eff e a p'')
      end
    end
  | (@seq_abs ?A ?B ?eff ?args ?rets ?C _ ?step ?z ?state ?st, ?p) =>
    let x := (eval cbv beta in (p (dummy _ _ i) (dummy _ _ (S i)))) in
    let p' := reconstruct x (S (S i)) in
    lazymatch (eval pattern (dummy _ A i), (dummy _ state (S i)) in p') with
    | ?p'' _ _ =>
      constr:(@step_state A B _ _ eff args rets _ step st z p'')
    end
  | (@bind ?T ?T' ?eff ?args ?rets, ?p, ?g) =>
    let x := (eval cbv beta in (g (dummy _ _ i))) in
    let q := reconstruct x (S i) in
    let q' := reconstruct p i in
    lazymatch (eval pattern (dummy _ T i) in q) with
    | ?g' _ =>
      constr:(@bind T T' eff args rets q' g')
    end
  | (@sum_merge ?A ?B, ?fl, ?fr, ?o) =>
    let xl := (eval cbv beta in (fl (dummy _ _ i))) in
    let ql := reconstruct xl (S i) in
    let xr := (eval cbv beta in (fr (dummy _ _ i))) in
    let qr := reconstruct xr (S i) in
    lazymatch (eval pattern (dummy _ A i) in ql) with
    | ?pl' _ =>
      lazymatch (eval pattern (dummy _ B i) in qr) with
      | ?pr' _ => constr:(@sum_merge A B _ pl' pr' o)
      end
    end
  | (@option_branch ?A ?B, ?f, ?f0, ?o) =>
    let q := reconstruct f0 i in
    let x := (eval cbv beta in (f (dummy _ _ i))) in
    let p' := reconstruct x (S i) in
    lazymatch (eval pattern (dummy _ A i) in p') with
    | ?p'' _ =>
      constr:(@option_branch A B p'' q o)
    end
  | (@prod_curry ?A ?B, ?f, ?o) =>
    let x := (eval cbv beta in (f (dummy _ _ i) (dummy _ _ (S i)))) in
    let q := reconstruct x (S (S i)) in
    lazymatch (eval pattern (dummy _ A i), (dummy _ B (S i)) in q) with
    | ?p' _ _ =>
      constr:(let (_a,_b) := o in p' _a _b)
    end
  | (@nat_rect_nondep ?A, ?f, ?f0, ?n, ?a) =>
    let x := (eval cbv beta in (f (dummy _ _ i))) in
    let y := (eval cbv beta in (f0 (dummy _ _ i) (dummy _ _ (S i)) (dummy _ _ (S (S i))))) in
    let f' := reconstruct x (S i) in
    let f0' := reconstruct y (S (S (S i))) in
    (*    let ty := type of a in*)
    lazymatch A with
      ?ty -> _ =>
      lazymatch (eval pattern (dummy _ ty i) in f') with
      | ?f'' _ =>
        lazymatch (eval pattern (dummy _ nat i), (dummy _ A (S i)), (dummy _ ty (S (S i))) in f0') with
        | ?f0'' _ _ _ =>
          constr:(@nat_rect_nondep A f'' f0'' n a)
        end
      end
    end
  | (@list_rec_nondep ?A, ?B, ?f, ?f0, ?l, ?a) =>
    let x := (eval cbv beta in (f (dummy _ _ i))) in
    let y := (eval cbv beta in (f0 (dummy _ _ i) (dummy _ _ (S i)) (dummy _ _ (S (S i))) (dummy _ _ (S (S (S i)))))) in
    let f' := reconstruct x (S i) in
    let f0' := reconstruct y (S (S (S (S i)))) in
    let ty := type of a in
    lazymatch (eval pattern (dummy _ ty i) in f') with
    | ?f'' _ =>
      lazymatch (eval pattern (dummy _ A i), (dummy _ (list A) (S i)), (dummy _ B (S (S i))), (dummy _ ty (S (S (S i)))) in f0') with
      | ?f0'' _ _ _ _ =>
        constr:(@list_rec_nondep A B f'' f0'' l a)
      end
    end
  | _ => tree
  end.

Ltac coro_to_state p :=
  let x := to_dummy 0 p in
  lazymatch x with
  | context [@coro_type ?A ?B ?C ?state ?step] =>
    lazymatch (eval pattern (@coro_type A B C state step) in x) with
    | ?F _ =>
      let y := (eval cbv beta in (F state)) in
      reconstruct y 0
    end
  end.

Transparent proc_coro.

Ltac get_step c :=
  let step := open_constr:(_) in
  let _ := constr:(ltac:(auto with equivc) : equiv_coro step _ c) in
  step.

Ltac derive_coro env :=
  lazymatch goal with
    |- _ ?step ?init _ =>
    let u := open_constr:(inl env) in
    unify init u
  end;
  let r := fresh in
  repeat eexists; try econstructor; [| intros; try dest_step];
  intro r; derive_core (*open_constr:(fun x => inr x)*) (env,r);
    lazymatch goal with
      |- equiv' ?step (fun _ op _ => _ /\ op = None) _ (Return ?r) _ =>
      ( let ptr := next_ptr in
         eapply (Equiv'Return _ _ (ptr r));
         unfold sum_merge;
         cbv beta iota;
         split;
         lazymatch goal with
           |- _ ?x = _ =>
           pattern_rhs x;
           eapply eq_refl
         | _ => eapply eq_refl
         end)
      || (eapply Equiv'Return;
          unfold sum_merge;
          cbv beta iota;
          split;
          lazymatch goal with
            |- _ ?x = _ =>
            pattern_rhs x;
            eapply eq_refl
          | _ => eapply eq_refl
          end)
    | _ => eapply Equiv'Return;
          unfold sum_merge;
          cbv beta iota;
          split;
          lazymatch goal with
            |- _ ?x = _ =>
            pattern_rhs x;
            eapply eq_refl
          | _ => eapply eq_refl
          end
    end
.

Instance ternary_Inhabit (A B C:Set) `{ Inhabit A } : Inhabit (ternary A B C) :=
  { inhabitant := tnr1 inhabitant }.

Lemma ex_coroutine_derive :
  { state & { step & forall k, { init | @equiv_coro _ _ _ _ _ state step init (ex_coroutine k) }}}.
  do 3 eexists.
  unfold ex_coroutine.
  unshelve derive_coro (tt,k); exact inhabitant.
Defined.

Definition ex_coroutine_step :=
  projT1 (projT2 ex_coroutine_derive).

Definition ex_coroutine_equiv k :
  equiv_coro ex_coroutine_step (inl (tt,k)) (ex_coroutine k) :=
  proj2_sig (projT2 (projT2 ex_coroutine_derive) k).

Hint Resolve ex_coroutine_equiv : equivc.

Definition ex_coro' n : t (const_yield nat) (const_yield nat) (option nat) :=
  k <- yield n;
    if Nat.leb k n then
      Return (Some k)
    else Return None.

Instance sum_inhabitant A B `{IB : Inhabit B} : Inhabit (A + B) :=
  { inhabitant := inr inhabitant }.

Lemma ex_coro'_derive :
  { state & { step & { init | @equiv_coro _ _ _ _ _ state step init ex_coro' } } }.
Proof.
  do 3 eexists.
  unfold ex_coro'.
  unshelve derive_coro tt; exact inhabitant.
Defined.

Definition ex_coroutine2 n : t (const_yield nat) (const_yield nat) unit :=
  k'' <- yield n;
    o <<- ex_coro' k'';
    match o with
    | Some k =>
      _ <- yield k;
        Return tt
    | None => Return tt
    end.

Lemma ex_coroutine2_derive :
  { state :Set & { step & { init | @equiv_coro _ _ _ _ _ state step init (ex_coroutine2) }}}.
  unfold ex_coroutine2.
  do 3 eexists.
  unshelve derive_coro tt; exact inhabitant.
  Grab Existential Variables.
  all: exact inhabitant.
Defined.

Lemma GenForall2_nth_Some_list_equiv_coro :
  forall (A B:Set) (IA : Inhabit A) (IB : Inhabit B) state
         (step : step_type (const_yield A) (const_yield B) unit state)
         x1 x2 n a1 a2,
    GenForall2 (F := list)(fun (coro : coro_type step) (st : state) =>
                  equiv_coro step st coro) x1 x2 ->
    nth_err _ x1 n = Some a1 ->
    nth_err _ x2 n = Some a2 ->
    equiv_coro step a2 a1.
Proof.
  intros.
  eapply (GenForall2_nth_Some (F := list)(R := (fun (coro : coro_type step) (st : state) => equiv_coro step st coro))); eauto.
Qed.

Hint Resolve GenForall2_nth_Some_list_equiv_coro : foldable.

Ltac generalize_and_ind :=
  lazymatch goal with
    |- nat_rect_nondep ?f ?f0 ?k (?a,?l) = nat_rect_nondep ?f' ?f0' _ (_,?l') =>
    lazymatch type of f with
    | context [@coro_type _ _ _ ?state ?step] =>
      let x0 := fresh in
      set (x0 := f0);
      let x := fresh in
      set (x := f);
      let y0 := fresh in
      set (y0 := f0');
      let y := fresh in
      set (y := f');
      let H := fresh "__k" in
      cut (GenForall2 (fun (coro : coro_type step) (st : state) => equiv_coro step st coro) l l');
      [ generalize l l' a;
        generalize k as H;
        subst x; subst x0; subst y; subst y0
       |unfold GenForall2; (solve [simpl; eauto with foldable equivc] || (eexists; split; [reflexivity| solve [simpl; eauto with foldable equivc]]))];
      induction H; intros;
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
  | |- nat_rect_nondep ?f0 _ ?k ?l = nat_rect_nondep _ _ _ ?l' =>
    lazymatch type of f0 with
    | context [@coro_type _ _ _ ?state ?step] =>
        cut (GenForall2 (fun (coro : coro_type step) (st : state) => equiv_coro step st coro) l l');
      [ generalize l l'
       |unfold GenForall2; eexists; split; [reflexivity| solve [simpl; eauto with equivc]]];
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
  | |- list_rec_nondep _ _ ?l ?a = list_rec_nondep _ _ _ ?a' =>
    lazymatch type of a with
    | context [@coro_type _ _ _ ?state ?step] =>
      cut (GenForall2 (fun (coro: coro_type step)(st : state) => equiv_coro step st coro) a a');
      [ generalize a a'
      | unfold GenForall2; eexists; split; [reflexivity| solve [simpl; eauto with equivc]]];
      induction l; intros;
      lazymatch goal with
        |- list_rec_nondep ?f ?f0 _ _ = list_rec_nondep ?f' ?f0' _ _ =>
        let tmp := fresh in
        set (tmp := f);
        let tmp' := fresh in
        set (tmp' := f');
        let tmp0 := fresh in
        set (tmp0 := f0);
        let tmp0' := fresh in
        set (tmp0' := f0');
        simpl list_rec_nondep;
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
    assert (equiv_coro step st c) as (H,H0) by eauto with foldable equivc;
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
      let s0 := fresh in
      let op0 := fresh in
      let o0 := fresh in
      let H3 := fresh in
      let H4 := fresh in
      inversion H1 as [|s0 op0 o0 (H3,H4)]; subst;
      unfold proc_coro at 1, seqE at 1;
      lazymatch goal with
        H_ : _ = c x |- _ =>
        rewrite <- H_
      | |- match ?x with _ => _ end _ = _ =>
        let x' := eval red in x in
            change x with x'; simpl
      | _ =>
        idtac
      end
    end;
    dest_yield
  end.

Ltac dest_match :=
  lazymatch goal with
  | |- option_branch _ _ ?o = option_branch _ _ ?o0 =>
    lazymatch o with
    | ?o0 => destruct o eqn:?
    | _ =>
      destruct o eqn:?, o0 eqn:?;
               [|try (exfalso; solve [eauto with foldable])..|];
      unfold sum_merge
    end
  | |- sum_merge _ _ ?x = sum_merge _ _ ?y =>
    lazymatch x with
    | y => destruct x eqn:?
    | _ => destruct x eqn:?, y eqn:?;
                    [|try (exfalso; solve [eauto with foldable])..|];
           unfold option_branch
    end
  | |- match ?o with _ => _ end = option_branch _ _ ?o0 =>
    destruct o eqn:?, o0 eqn:?;
         [|try (exfalso; solve [eauto with foldable])..|];
    unfold option_branch
  | |- match ?x with _ => _ end = match ?y with _ => _ end =>
    lazymatch x with
    | y => destruct x eqn:?
    | _ => destruct x eqn:?, y eqn:?;
             [|try (exfalso; solve [eauto with foldable])..|]
    end
  end.

Notation "'let_coro' x := c 'in' p" :=
  (pipe (c : coro_type ltac:(let step := get_step c in exact step))
        (fun x => p))
    (at level 200, only parsing).

Ltac mid_eq_core :=
  discriminate
  || dest_match
  || proc_step
  || apply eq_refl
  || (progress (repeat match goal with
                       | H : _ |- _ => apply H
                       end);
      ((simpl in *; congruence) || solve [eauto with foldable equivc] || solve [simpl; eauto]))
  || generalize_and_ind
  || lazymatch goal with
       |- Eff ?e ?a ?f = Eff _ _ ?f0 =>
       apply (@f_equal _ _ (fun x => Eff e a x) f f0);
       let H := fresh in
       extensionality H
     | |- bind ?a ?p  = bind _ ?p0 =>
       apply (@f_equal _ _ (fun x => bind a x) p p0);
       let H := fresh in
       extensionality H
     end
  || eauto with foldable equivc.

(*
Ltac mid_eq_core :=
  dest_match
  || proc_step
  || (repeat match goal with
             | H : _ |- _ => apply H
             end;
      ((simpl in *; congruence) || solve [eauto with foldable equivc] || solve [simpl; eauto]))
  || generalize_and_ind
  (*
  || (exfalso; solve [eauto with foldable])
*)
  || lazymatch goal with
       |- Eff _ _ _ = Eff _ _ _ =>
       f_equal;
       let H := fresh in
       extensionality H
     | |- (_ <<- _ ; _) = (_ <<- _ ; _ ) =>
       f_equal;
       let H := fresh in
       extensionality H
     end.
*)

Definition loop_ex (p : nat * nat)(n i : nat) : t args_effect rets_effect (option unit):=
  let_coro c0 := ex_coroutine 0 in
      nat_rect_nondep
        (fun l =>
          match nth_err _ l i : option (@coro_type nat nat _ _ _) with
           | Some c =>
             r <- resume c $ 1;
               putN r;
               let (a,b) := p in
               putN a;
               Return (Some tt)
           | None => Return None
           end)
        (fun m rec l =>
           putN (0:args_effect putNat);
             pipe (ex_coroutine m : @coro_type nat nat _ _ _)
                  (fun cm =>
                     rec (cm::l)))
        n [c0].


Ltac derive' env :=
  lazymatch goal with
    |- equiv ?step ?init ?x =>
    let u := open_constr:(inl env) in
    simpl;
    unify init u;
    repeat eexists;
    [ dest_step
    | derive_core env];
    let ptr := next_ptr in
    lazymatch goal with
      |- equiv' ?step _ _ (Return ?r) _ =>
      apply (Equiv'Return step _ (ptr r) None);
      simpl;
      split;
      lazymatch goal with
        |- _ ?x = _ =>
        pattern_rhs x;
        apply eq_refl
      | _ => apply eq_refl
      end
    end
  end.

Definition simple_double_loop : t args_effect rets_effect _ :=
  n <- getN;
    nat_rect_nondep
      (fun ls => Return (Some ls))
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
  unshelve derive' tt; intros; exact inhabitant.
Defined.

Definition prod_ex (p : nat * nat) : t args_effect rets_effect _ :=
  let (n,m) := p in
  putN n;
    putN m;
    Return (Some tt).

Definition prod_ex_derive p :
  { state & { step & { init | @equiv _ _ _ _ state step init (prod_ex p)}}}.
  do 3 eexists.
  unfold prod_ex.
  unshelve derive' (tt,p); intros; exact inhabitant.
Defined.
  
Definition list_ex :=
  n <- getN;
    list_rec_nondep
      (fun a => Return (Some a))
      (fun x l rec a =>
         putN 0;
           rec (a + x)%nat
               (*
         if Nat.even x then
           rec (a + x)%nat
         else
           Return (Some a) *))
      (seq 0 n) 0.

Definition list_ex_derive :
  { state & { step & { init | @equiv _ _ _ _ state step init list_ex}}}.
Proof.
  do 3 eexists.
  unfold list_ex.
  unshelve derive' tt; intros; exact inhabitant.
Defined.

Ltac derive env :=
  lazymatch goal with
    |- equiv ?step ?init ?x =>
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
    [ dest_step
    | derive_core env ]
  | |- _ ?step ?init _ =>
    let u := open_constr:(inl env) in
    unify init u;
    econstructor;
    econstructor;
    [|intros; dest_step];
    let r := fresh in
    intro r;
    let H := fresh in
    lazymatch goal with
      |- _ ?x _ =>
      assert (x = ltac:(let x' := eval red in x in
                            let x'' := coro_to_state x' in exact x''))
        as H by
            (change x with ltac:(let x0 := eval red in x in exact x0);
             unfold pipe;
             repeat mid_eq_core);
      rewrite H;
      clear H;
      unfold step_state;
      derive_core (env,r)
    end
  end;
  lazymatch goal with
    |- equiv' ?step _ _ (Return ?r) _ =>
    (let ptr := next_ptr in
     eapply (Equiv'Return step _ (ptr r));
     simpl;
     split;
     lazymatch goal with
       |- _ ?x = _ =>
       pattern_rhs x;
       eapply eq_refl
     | _ => eapply eq_refl
     end)
    || (eapply (Equiv'Return step);
        simpl;
        split;
        lazymatch goal with
          |- _ ?x = _ =>
          pattern_rhs x;
          eapply eq_refl
        | _ => eapply eq_refl
        end)
  end.

Definition loop_ex_derive p n i :
  { state & { step & { init | @equiv _ _ _ _ state step init (loop_ex p n i) }}}.
Proof.
  do 3 eexists.
  unshelve derive (tt,p,n,i); intros; exact inhabitant.
Defined.

Definition coro' n : t (const_yield nat) (const_yield nat) (option unit) :=
  k <- yield n;
  pipe (ex_coroutine n : @coro_type nat nat _ _ ex_coroutine_step)
       (fun c =>
            m <- resume c $ k;
            _ <- yield m;
            Return None).

(*
Definition coro'_derive :
  { state & {step & { init | @equiv_coro _ _ _ state step init coro'}}}.
Proof.
  do 3 eexists.
  lazymatch goal with
    |- equiv_coro _ ?init ?x =>
    let u := open_constr:(inl tt) in
    unify init u
  end;
  econstructor.
  econstructor.
  intros.
  split.
  dest_step.

  assert (coro' r = ltac:(let x' := eval red in (coro' r) in
                              let x'' := coro_to_state x' in exact x'')).
  unfold coro', pipe.
  repeat mid_eq_core.
  rewrite H.
  unfold step_state.

  derive_core open_constr:(fun a => inr a) (tt,r);
  let ptr := next_ptr open_constr:(fun _x => _x) in
  lazymatch goal with
    |- equiv' ?step _ _ (Return ?r) _ =>
    apply (Equiv'Return step _ (ptr r) None);
      simpl;
      split;
      lazymatch goal with
        |- _ ?x = _ =>
        pattern_rhs x;
          apply eq_refl
      | _ => apply eq_refl
      end
  end.
Defined.
 *)

(*
Definition loop_ex2 n : t args_effect rets_effect (option unit) :=
  let_coro c0 := ex_coroutine 0 in
  let_coro c1 := ex_coroutine 1 in
  nat_rect_nondep
    (fun _ => Return (Some tt))
    (fun n' rec l =>
       list_rec_nondep
         (fun l0k => rec (fst l0k))
         (fun (c:@coro_type nat nat _ _ _) _ rec l0k =>
            r <- resume c $ 0;
              putN r;
              let l0' := replace_list (snd l0k) c (fst l0k) in
              rec (l0',S (snd l0k)))
         l (l,0)
    )
    n [c0;c1].

Definition loop_ex2_derive n :
  { state & { step & { init | @equiv _ _ _ _ state step init (loop_ex2 n) }}}.
Proof.
  do 3 eexists.
  lazymatch goal with
    |- equiv _ ?init ?x =>
    let u := open_constr:(inl (tt,n)) in
    unify init u;
    let H := fresh in
    assert (x = ltac:(let x' := eval red in x in
                          let x'' := coro_to_state x' in exact x''))
  end.
  unfold loop_ex2.
  unfold pipe.
  repeat mid_eq_core.
  (*
  unfold loop_ex2.
  match goal with
    |- equiv _ _ ?p =>
    let x := to_dummy 0 p in
    lazymatch x with
    | context ctr [@coro_type ?A ?B ?state ?step] =>
        lazymatch (eval pattern (@coro_type A B state step) in x) with
        | ?F _ => 
        let y := (eval cbv beta in (F state)) in
        reconstruct y 0
        end
    end
  end.
   *)
  generalize_and_ind.
  unshelve derive (tt,n); exact unit.
Defined.
 *)

Lemma GenForall2_bsearch_Some_equiv_coro :
  forall (A B C : Set) (IA : Inhabit A) (IB : Inhabit B) (state : Set)
         (step : step_type (const_yield A) (const_yield B) C state)
         x1 x2 n a1 a2,
    GenForall2 (fun (coro : coro_type step) (st : state) => equiv_coro step st coro) x1 x2 ->
    bsearch n x1 = Some a1 ->
    bsearch n x2 = Some a2 ->
    equiv_coro step a2 a1.
Proof.
  intros.
  eapply (GenForall2_bsearch_Some (R := fun c s => equiv_coro step s c)).
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
               match bsearch key m' : option (@coro_type nat nat _ _ _) with
               | Some c =>
                 n <- getN;
                   r <- resume c $ n;
                   putN r;
                   rec (replace_map key c m')
               | None => rec m'
               end)
          fuel (Node ("key",c) (Leaf _) (Leaf _)).

Hint Constructors ex equiv'.
Hint Unfold equiv_coro.

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
  unshelve derive (tt,fuel); intros; exact inhabitant.
  Grab Existential Variables.
  all: exact inhabitant.
Defined.


Definition echo name s :
  t (const_yield String.string) (const_yield String.string) unit :=
  s' <- yield (String.append (String.append s " from ") name);
    _ <- yield (String.append (String.append s' " from ") name);
    Return tt.

Lemma echo_derive :
  { state & { step & forall name, { init | @equiv_coro _ _ _ _ _ state step init (echo name) }}}.
Proof.
  do 3 eexists.
  unfold echo.
  unshelve derive_coro (tt,name); exact inhabitant.
  Grab Existential Variables.
  all: exact inhabitant.
Defined.

Definition echo_step := projT1 (projT2 echo_derive).

Definition echo_equiv n : equiv_coro echo_step (inl (tt,n)) (echo n) :=
  proj2_sig (projT2 (projT2 echo_derive) n).

Hint Resolve echo_equiv : equivc.

Definition sendHello fuel : t args_effect rets_effect (option unit) :=
  let_coro c0 := echo "c0" in
  let_coro c1 := echo "c1" in
  nat_rect_nondep
    (fun _ => Return (Some tt))
    (fun _ rec m =>
       key <- getStr;
         match bsearch key m : option (@coro_type String.string String.string _ _ _) with
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
  unshelve derive (tt,fuel); intros; exact inhabitant.
Defined.

Lemma GenForall2_insert : forall (A B : Set)(R : A -> B -> Prop)(m1 : Map A) m2 a b n,
    GenForall2 R m1 m2 ->
    R a b ->
    GenForall2 R (insert n a m1) (insert n b m2).
Proof.
  intros.
  apply GenForall2_Forall2_map in H.
  apply GenForall2_Forall2_map.
  revert m2 H.
  induction m1; intros.
  inversion H. subst.
  simpl.
  destruct (lebString n k).
  constructor; auto.
  constructor; auto.
  inversion H. subst.
  constructor; auto.
Qed.

Hint Resolve GenForall2_insert : foldable.

Definition tree_ex fuel : t args_effect rets_effect (option unit) :=
  nat_rect_nondep
    (fun _ => Return (Some tt))
    (fun _ rec tr =>
       key <- getStr;
         let oc := bsearch key tr : option (@coro_type nat nat _ _ _) in
         match oc with
         | Some c =>
           r <- resume c $ 0;
             putN r;
             let tr' := replace_map key c tr in
             rec tr'
         | None => 
           pipe (ex_coroutine 0 : @coro_type nat nat _ _ ex_coroutine_step)
                (fun c =>
                   rec (insert key c tr))
         end)
    fuel (Leaf (@coro_type nat nat _ _ ex_coroutine_step)).

Lemma tree_ex_derive fuel :
  {state & {step & {init | @equiv _ _ _ _ state step init (tree_ex fuel)}}}.
Proof.
  do 3 eexists.
  unshelve derive (tt,fuel); intros; exact inhabitant.
Defined.

Definition tree_ex2 fuel fuel' : t args_effect rets_effect (option unit) :=
  nat_rect_nondep
    (fun _ => Return None)
    (fun _ rec tr =>
       key <- getStr;
         k <- getN;
         let oc := bsearch key tr : option (@coro_type nat nat _ _ _ ) in
         match oc with
         | None =>
           pipe (ex_coroutine 0 : @coro_type nat nat _ _ ex_coroutine_step)
                (fun c => rec (insert key c tr))
         | Some c =>
           nat_rect_nondep
              (fun tr => Return None)
              (fun _ rec_inner nc =>
                 let (n,c) := (nc : nat * @coro_type nat nat _ _ ex_coroutine_step) in
                 r <- resume c $ n;
                   putN 0;
                   if r =? 0 then
                     let tr' := replace_map key c tr in
                     rec tr'
                   else
                     rec_inner (S n, c))
              fuel' (k,c)
         end)
    fuel (Leaf (@coro_type nat nat _ _ ex_coroutine_step)).


Program Instance id_HasGenForall2 : HasGenForall2 (fun A:Set => A) :=
  { GenForall2 := fun A1 A2 R => R }.

Lemma tree_ex2_derive fuel fuel' :
  {state & {step & {init | @equiv _ _ _ _ state step init (tree_ex2 fuel fuel')}}}.
Proof.
  do 3 eexists.
  unshelve derive (tt,fuel,fuel'); intros; exact inhabitant.
Defined.

Definition echo_loop fuel name s :
  t (const_yield String.string) (const_yield String.string) unit :=
    nat_rect_nondep
      (fun _ => Return tt)
      (fun fuel' rec s =>
         s' <- yield (String.append s name);
           rec s')
      fuel s.

Lemma echo_loop_derive :
  { state & { step & forall fuel name, { init | @equiv_coro _ _ _ _ _ state step init (echo_loop fuel name) }}}.
Proof.
  do 3 eexists.
  unfold echo_loop.
  unshelve derive_coro (tt,fuel,name); intros; exact inhabitant.
Defined.