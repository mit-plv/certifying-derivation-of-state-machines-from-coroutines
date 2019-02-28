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
Definition label (A:Type)(_:A) := True.

Ltac put_label x :=
  assert (label x) by (unfold label; auto).

Ltac free_var' exp env cont :=
  let rec aux env :=
      lazymatch env with
      | (?env',?x) =>
        lazymatch exp with
        | context[x] =>
          let env'' := aux env' in
          constr:((env'',x))
        | _ =>
          aux env'
        end
      | _ => tt
      end
  in
  let e := aux env in
  cont e.
          (*
          Ltac free_var' exp env cont :=
  lazymatch exp with
  | Fix ?f =>
    lazymatch type of f with
    | nat -> _ =>
      let eO := (eval simpl in (f O)) in
      let eS := (eval simpl in (f (S inhabitat))) in
      free_var' eO env ltac:(fun x =>
                               free_var' eS env
                                         ltac:(fun y =>
                                            let v := merge x y in
                                            cont v))
    | list nat -> _ =>
      let eN := (eval simpl in (f [])) in
      let eC := (eval simpl in (f (inhabitat::inhabitat))) in
      free_var' eN env ltac:(fun x =>
                               free_var' eC env
                                         ltac:(fun y =>
                                                 let v := merge x y in
                                                 cont v))
    end
  | ?f ?x =>
    free_var' f env ltac:(fun v1 =>
                            free_var' x env
                                      ltac:(fun v2 =>
                                         let v := merge v1 v2 in
                                         cont v))
  | (fun x => _) =>
    let exp' := (eval simpl in (exp inhabitat)) in
    free_var' exp' env cont
  | (match ?m with O => ?e1 | S m' => ?e2 end) =>
    lazymatch constr:(_ : forall m':nat, @reify_cls _ e2) with
    | ?e =>
      let exp' := (eval simpl in (e inhabitat)) in
      free_var' e1 env ltac:(fun x =>
                               free_var' exp' env
                                         ltac:(fun y =>
                                            let v := merge x y in
                                            let b := mem m env in
                                            lazymatch b with
                                            | true =>
                                              let r := merge v constr:((v,m)) in
                                              cont r
                                            | false => cont v
                                            end))
    end
  | _ =>
    match goal with
    | H : label ?exp' |- _ =>
      tryif constr_eq exp exp' then
        clear H;
        free_var' (Fix exp) env cont;
        put_label exp'
      else fail
    | _ =>
      tryif is_var exp then
        let b := mem exp env in
        lazymatch b with
        | true => cont (tt,exp)
        | false => cont tt
        end
      else
        cont tt
    end
  end.
  *)

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
    match goal with
    | H : label ?exp' |- _ =>
      tryif constr_eq exp exp' then
        clear H;
        free_var (Fix exp) env
      else fail
    | _ =>
      tryif is_var exp then
        let b := mem exp env in
        lazymatch b with
        | true => constr:((tt,exp))
        | false => constr:(tt)
        end
      else
        constr:(tt)
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
        let ty := type of prev in
        free_var' p (env,prev)
                  ltac:(fun x__ =>
                          let b := mem prev x__ in
                          lazymatch b with
                          | true =>
                            let e := open_constr:(fun x:ty => ptr (inl (env,x))) in
                            let e' := (eval simpl in e) in
                            unify f e';
                            eapply EquivEff;
                            [ dest_step
                            | intros;
                              derive' (env,prev)]
                          | false =>
                            let e := open_constr:(fun _:ty => ptr (inl env)) in
                            let e' := (eval simpl in e) in
                            unify f e';
                            eapply EquivEff;
                            [ dest_step
                            | intros; derive' env ]
                          end)
      end
    | match ?m with O => _ | S m' => _ end =>
      lazymatch current with
      | ?f ?prev =>
        let m' := fresh in
        let ty := type of prev in
        let e :=
            lazymatch prev with
            | m => open_constr:(fun x => match x return state with O => _ O | S m' => _ m' end)
            | _ => open_constr:(match m return ty -> state with O => _ | S m' => _ end)
            end
        in
        unify f e;
        destruct m
      end
    | ?fn ?m =>
      lazymatch current with
      | ?f ?prev =>
        let rec aux fn accum :=
            lazymatch fn with
            | Fix ?fx =>
              let ty := type of prev in
              let x' := fresh "x" in
              lazymatch prev with
              | m =>
                let e := open_constr:(fun x =>
                                        match x return state with
                                          O => _ x
                                        | S x' => _ x
                                        end)
                in
                unify f e;
                simpl;
                let tmp := fresh in
                let tmp' := fresh in
                set (tmp := fn);
                set (tmp' := step);
                lazymatch goal with
                  |- equiv _ ?c _ =>
                  cut (label c); [|unfold label; auto];
                  pattern m at 1;
                  lazymatch goal with
                    |- (fun n:nat => label ?body -> _) _ =>
                    lazymatch constr:(_ : forall n:nat, @reify_cls _ body) with
                    | ?res =>
                      simpl; intros;
                      let tmp'' := fresh in
                      set (tmp'' := res);
                      fold (tmp'' m);
                      let m' := fresh in
                      generalize m at 1 2 as m';
                      subst tmp;
                      subst tmp';
                      subst tmp'';
                      intro m';
                      accum;
                      unfold Fix at 1;
                      put_label fx;
                      induction m';
                      intros
                    end
                  end
                end
              | _ =>
                let a := fresh in
                let m0 := fresh in
                let e :=
                    lazymatch type of m with
                    | nat => 
                      open_constr:(fun x:ty => match m return state with
                                     O => _ x
                                   | S m0 => _ x
                                   end)
                    | list nat =>
                      open_constr:(fun x:ty => match m return state with
                                   | [] => _ x
                                   | a::m0 => _ x
                                   end)
                    end
                in
                unify f e;
                simpl;
                let tmp := fresh in
                let tmp' := fresh in
                let m' := fresh in
                set (tmp := fn);
                set (tmp' := step);
                (generalize m at 1 4 as m' || generalize m at 1 2 as m');
                subst tmp;
                subst tmp';
                intro m';
                accum;
                unfold Fix at 1;
                put_label fx;
                induction m';
                intros
              end
            | ?fn' ?a =>
              aux fn' ltac:(generalize a; accum)
            | _ =>
              let a := fresh in
              let e := open_constr:(fun a => _) in
              unify f e;
              simpl;
              eauto
            end
        in
        aux fn idtac
      end
    end
  end.

Definition ex1 : t effect unit:=
  n <- get;
    put n;
    put n;
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


Definition readL (f : list nat -> t effect unit) :=
  Fix (fix readL accum n :=
         match n with
         | O => f accum
         | S n' =>
           x <- get;
             readL (accum ++ [x]) n'
         end).


Definition printL (e : t effect unit) :=
  Fix (fix printL l :=
    match l with
    | [] => e
    | a::l' =>
      put a;
        printL l'
    end).

Theorem ex3: {state & {step & {init | @equiv state _ step init
                                             (m <- get;
                                                n <- get;
                                                put 0;
                                        Fix (fix f y :=
                                           match y with
                                           | O => put n; put m; Pure _ tt
                                           | S y' => put y; f y'
                                           end) (m + n)%nat)}}}.
Proof.
  do 2 eexists.
  eexists ?[init].
  let e := open_constr:(inl tt) in
  unify ?init e.
  derive' tt.
  derive' (tt,x0,x).
  derive' (tt,H3,x0,x).
  apply IHnat.
  Grab Existential Variables.
  all: exact unit || exact (fun _ => None).
Defined.

Theorem ex_read: {state & {step & forall l', {init |
                       @equiv state _ step init
                              (n <- get;
                                 readL (fun l => put (length l); Pure _ tt)
                                       l' n) }}}.
Proof.
  unfold readL.
  do 2 eexists.
  intros.
  eexists ?[init].
  let e := open_constr:(inl (tt,l')) in
  unify ?init e.
  derive' (tt,l').
  derive' (tt,l'0).
  derive' (tt,l'0,H3).
  Grab Existential Variables.
  all: exact unit || exact (fun _ => None).
Defined.

Eval cbv [prod_curry ex_read sum_merge projT1 projT2] in projT1 (projT2 ex_read).

Goal {state & {step & forall l,
                  {init |
                   @equiv state _ step init
                          (put (length l); printL (Pure _ tt) l)}}}.
Proof.
  unfold printL.
  do 2 eexists.
  intros.
  eexists ?[init].
  let e := open_constr:(inl (tt,l)) in
  unify ?init e.
  derive' (tt,l).
  derive' tt.
  derive' (tt, a, H3).
  eapply IHlist.
  Grab Existential Variables.
  all: exact unit || exact (fun _ => None).
Defined.

Goal {state & {step & forall l',
                  {init |
                   @equiv state _ step init
                   (n <- get;
                      readL (fun l => printL (Pure _ tt) l) l' n) }}}.
Proof.
  unfold readL, printL.
  do 2 eexists.
  intros.
  eexists ?[init].
  let e := open_constr:(inl (tt,l')) in
  unify ?init e.
  derive' (tt,l').
  derive' (tt,l'0).
  derive' tt.
  derive' (tt,a,H5).
  apply IHlist.
  derive' (tt,l'0,H3).
  Grab Existential Variables.
  all: exact unit || exact (fun _ => None).
Defined.

Theorem ex4:
  {state & {step & {init |
                    @equiv state _ step init
                           (k <- get;
                              l <- get;
                              n <- get;
                              Fix (fix f z y x :=
                                     match x with
                                     | O =>
                                       put y; Pure _ tt
                                     | S x' =>
                                       put 0;
                                       f (S z) (z + y)%nat x'
                                     end) l k n) }}}.
Proof.
  do 2 eexists.
  eexists ?[init].
  let e := open_constr:(inl tt) in
  unify ?init e.
  derive' tt.
  derive' (tt,x2).
  derive' (tt,x2,x3,H3).
  Grab Existential Variables.
  all: exact unit || exact (fun _ => None).
Defined.

Eval cbv [ex4 sum_merge prod_curry projT2 projT1] in projT1 (projT2 ex4).



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


Notation "l <- 'read' ( l0 , n ) ; e" := (readL (fun l => e) l0 n) (at level 100, right associativity).
Notation "'print' l ; e" := (printL e l) (at level 100, right associativity).

Definition handshake l0 l1 pk sk :=
  n <- get;
    m <- get;
    let key := generateKey tt in
    let ourEphemeralPublic := fst key in
    let ourEphemeralSecret := snd key in
    print ourEphemeralPublic;
      theirEphemeralPublic <- read(l0, n);
      theirHandshakeSealed <- read(l1, m);
      let theirHandshake :=
          open theirHandshakeSealed theirEphemeralPublic ourEphemeralSecret
      in
      let p := splitAt n theirHandshake in
      let theirPK := fst p in
      let theirHandshakeRest := snd p in
      let hs := open theirHandshakeRest theirPK ourEphemeralSecret in
      let ourHandshake :=
          pk ++ seal (ourEphemeralPublic ++ theirEphemeralPublic) theirEphemeralPublic sk
      in
      print (seal ourHandshake theirPK ourEphemeralSecret);
        Pure _ tt.

Theorem handshake_derive :
  {state & {step &
            forall l0 l1 pk sk,
              {init |
               @equiv state _ step init (handshake l0 l1 pk sk) }}}.
Proof.
  unfold handshake, printL, readL.
  do 2 eexists.
  intros.
  eexists ?[init].
  let e := open_constr:(inl (tt,l0,l1,pk,sk)) in
  unify ?init e.
  derive' (tt,l0,l1,pk,sk).
  derive' (tt,l0,l1,pk,sk,x).
  derive' (tt,l2,l1,pk,sk,x).
  derive' (tt,l3,l1,l2,pk,sk,x).
  derive' tt.
  derive' (tt,a,H7).
  apply IHlist.
  derive' (tt,l3,l2,H5,pk,sk,x).
  derive' (tt,l2,l1,H4,pk,sk,x).
  unshelve derive' (tt,l0,l1,H3,pk,sk,x,a).
  all : exact unit || exact (fun _ => None ).
Defined.

Arguments existT {_ _}.

Eval cbv [handshake_derive projT1 projT2 sum_merge prod_curry] in projT1 (projT2 handshake_derive).