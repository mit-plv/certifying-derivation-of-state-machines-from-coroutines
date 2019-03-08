Require Import List PeanoNat Program.Basics FunctionalExtensionality.
Import ListNotations.
Set Universe Polymorphism.
Open Scope type_scope.
Set Implicit Arguments.

Class habitable (A : Type) :=
  { inhabitat : A }.

Instance nat_habitable : habitable nat :=
  { inhabitat := 0 }.

Instance list_habitable (A : Type) : habitable (list A) :=
  { inhabitat := @nil A }.

Instance pair_habitable (A B : Type) `(HA : habitable A, HB : habitable B) : habitable (A * B) :=
  { inhabitat := (inhabitat,inhabitat) }.

Instance unit_habitable : habitable unit :=
  { inhabitat := tt }.

Opaque inhabitat.

Definition sum_merge (A B C : Type)(f : A -> C)(g : B -> C)(x : sum A B) :=
  match x with
  | inl a => f a
  | inr b => g b
  end.

Definition LetIn (A B : Type) (f:A -> B) (x:A) := f x.
Notation "'Let' x := def 'in' body" := (LetIn (fun x => body) def) (at level 100).

Infix "|||" := sum_merge (at level 60).

Inductive t (eff : Type -> Type) (a : Type) :=
| Pure : a -> t eff a
| Eff : forall T, eff T -> (T -> t eff a) -> t eff a.

Inductive effect : Type -> Type :=
| getE : unit -> effect nat
| putE : nat -> effect unit
| genKeyE : unit -> effect (list nat * list nat).

Notation "n <- 'get' ; e" := (Eff (getE tt) (fun n => e)) (at level 100, right associativity).
Notation "'put' n ; e" := (Eff (putE n) (fun _ => e)) (at level 100).
Notation "'( k1 , k2 ) <- 'genKey' ; e" := (Eff (genKeyE tt) (fun k => let k1 := fst k in let k2 := snd k in e)) (at level 100, right associativity).

Definition step_range (state : Type) :=
  option {ty : Type & effect ty * (ty -> state) }.

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
    | context[x__] => true
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
Definition label' (A:Type)(_:A) := True.

Ltac put_label x :=
  assert (label x) by (unfold label; auto).

Ltac free_var exp env :=
  let rec aux exp env :=
      lazymatch env with
      | (?env',?x) =>
        lazymatch exp with
        | context[x] =>
          let env'' := aux exp env' in
          constr:((env'',x))
        | _ =>
          aux exp env'
        end
      | _ => tt
      end
  in
  let e := aux exp env in
  e.

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
        let fv := free_var p (env,prev) in
        let H := fresh in
        assert (label' fv) as H by (unfold label'; auto);
        repeat match goal with
               | X := ?def |- _ =>
                 lazymatch def with
                 | context [prev] =>
                   progress (unfold X in H)
                 end
               end;
        let fv_f :=
            lazymatch goal with
            | _: label' ?fv' |- _ =>
              lazymatch (eval pattern prev in fv') with
              | ?f _ => f
              end
            end
        in
        clear H;
        let e := open_constr:(fun x:ty => ptr (inl (fv_f x))) in
        let e' := (eval simpl in e) in
        unify f e';
        eapply EquivEff;
        [ dest_step
        | intros; derive' fv ]
      end
    | let (x1,x2) := ?x in _ =>
      destruct x
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
    | match ?m with None => _ | Some m' => _ end =>
      lazymatch current with
      | ?f ?prev =>
        let m' := fresh in
        let ty := type of prev in
        let e := open_constr:(fun x:ty => match m return state with None => _ x | Some m' => _ x end) in
        unify f e;
        destruct m
      end
    | (Let var := ?def in ?body) =>
      lazymatch current with
      | ?f ?prev =>
        let v := fresh in
        let ty := type of prev in
        let e := open_constr:(fun x:ty => let v := def in _ x) in
        unify f e;
        set (v := def);
        unfold LetIn
      end
    | ?fn ?m =>
      lazymatch current with
      | ?f ?prev =>
        let rec aux fn accum :=
            lazymatch fn with
            | Fix ?fx =>
              let ty := type of prev in
              let x' := fresh "x" in
              let H := fresh in
              assert (label' m) as H by (unfold label'; auto);
              repeat match goal with
                     | X := ?def |- _ =>
                            lazymatch def with
                            | context [prev] =>
                              progress (unfold X in H)
                            end
                     end;
              let mred :=
                  lazymatch goal with
                  | _: label' ?m' |- _ => m'
                  end
              in
              clear H;
              let mf :=
                  lazymatch (eval pattern prev in mred) with
                  | ?g _ => g
                  end
              in
              let a := fresh in
              let e :=
                  lazymatch type of m with
                  | nat =>
                    open_constr:(fun x:ty =>
                                   match mf x return state with
                                   | O => _ x
                                   | S x' => _ x
                                   end)
                  | list nat =>
                    open_constr:(fun x:ty =>
                                   match mf x return state with
                                   | [] => _ x
                                   | a::x' => _ x
                                   end)
                  end
              in
              let e' := (eval simpl in e) in
              unify f e';
              simpl;
              repeat match goal with
                     | X := _ |- _ =>
                            progress (fold X)
                     end;
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
                | |- (fun l:list nat => label ?body -> _) _ =>
                  lazymatch constr:(_: forall l:list nat, @reify_cls _ body) with
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

Definition exLetIn : t effect unit :=
  n <- get;
    Let m := S n in put m; put m; Pure _ tt.

Theorem exLetIn_derive :
  {state & {step & {init | @equiv state _ step init exLetIn}}}.
Proof.
  do 2 eexists.
  eexists ?[init].
  unfold exLetIn.
  let e := open_constr:(inl tt) in
  unify ?init e.
  derive' tt.
  unshelve derive' (tt,H).
  all: exact unit || exact (fun _ => None).
Defined.

Eval cbv [exLetIn_derive exLetIn prod_curry sum_merge] in exLetIn_derive.

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
                                        Fix (fix f y :=
                                           match y with
                                           | O => put n; put m; Pure _ tt
                                           | S y' => put y; f y'
                                           end) (m+n)%nat)}}}.
Proof.
  do 2 eexists.
  eexists ?[init].
  let e := open_constr:(inl tt) in
  unify ?init e.  
  derive' tt.
  derive' (tt,x,x0).
  derive' (tt,H4,x,x0).
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
  derive' (tt,l'0,H4).
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
  derive' (tt, a, H4).
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
  derive' (tt,a,H6).
  apply IHlist.
  derive' (tt,l'0,H4).
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
  derive' (tt,x2,x3,H4).
  Grab Existential Variables.
  all: exact unit || exact (fun _ => None).
Defined.

Eval cbv [ex4 sum_merge prod_curry projT2 projT1] in projT1 (projT2 ex4).



Parameter open : list nat -> list nat -> list nat -> list nat -> option (list nat).
Parameter seal : list nat -> list nat -> list nat -> list nat -> list nat.

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

Definition foo :=
  '(k1,k2) <- genKey;
    put 0;
    print k1;
    print k2;
    Pure _ tt.

Goal {state & {step & {init | @equiv state _ step init foo}}}.
Proof.
  unfold foo, printL.
  do 2 eexists.
  eexists ?[init].
  let e := open_constr:(inl tt) in
  unify ?init e.
  derive' tt.
  derive' (tt,x).
  derive' tt.
  derive' (tt,a,H6).
  apply IHlist.
  derive' (tt,a,H4,x).
  apply IHlist.
  Grab Existential Variables.
  all: exact unit || exact (fun _ => None).
Defined.


Definition handshake l0 l1 pk sk :=
  '(ourEphemeralPublic,ourEphemeralSecret) <- genKey;
    n <- get;
    m <- get;
    print ourEphemeralPublic;
      theirEphemeralPublic <- read(l0, n);
      theirHandshakeSealed <- read(l1, m);
      match open theirHandshakeSealed theirEphemeralPublic ourEphemeralSecret [1] with
      | None => put 0; Pure _ tt
      | Some theirHandshake =>
        Let p := splitAt n theirHandshake in
        Let theirPK := fst p in
        Let theirHandshakeRest := snd p in
        let hs := open theirHandshakeRest theirPK ourEphemeralSecret [2] in
        let ourHandshake :=
            pk ++ seal (ourEphemeralPublic ++ theirEphemeralPublic) theirEphemeralPublic sk [3]
        in
        print (seal ourHandshake theirPK ourEphemeralSecret [4]);
          Pure _ tt
      end.

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
  derive' (tt,l0,pk,sk,x,x0).
  derive' (tt,l2,l1,pk,sk,x,x0).
  derive' (tt,l3,l2,pk,sk,x,x0).
  derive' (tt,l3,l2,pk,sk,x,x0).
  derive' (tt,l3,l2,pk,sk,x,x0,H5).
  derive' tt.
  derive' (tt,a,H11).
  apply IHlist.
  derive' tt.
  derive' (tt,l3,l2,H8,pk,sk,x,x0).
  derive' (tt,l1,l2,H6,pk,sk,x,x0).
  derive' (tt,l0,l1,H4,pk,sk,x,x0,a).
  Grab Existential Variables.
  all : exact unit || exact (fun _ => None ).
Defined.

Arguments existT {_ _}.

Eval cbv [handshake_derive projT1 projT2 sum_merge prod_curry] in projT1 (projT2 handshake_derive).


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

Extract Constant open =>
  "\msg pk sk nonce -> boxOpen (fromJust $ decode $ pack $ map fromIntegral pk) (fromJust $ decode $ pack $ map fromIntegral sk) (fromJust $ decode $ pack $ map fromIntegral nonce) (pack $ map fromIntegral msg)".
Extract Constant seal =>
  "\msg pk sk nonce -> box (fromJust $ decode $ pack $ map fromIntegral pk) (fromJust $ decode $ pack $ map fromIntegral sk) (fromJust $ decode $ pack $ map fromIntegral nonce) (pack $ map fromIntegral msg)".

Extraction "Handshake.hs" handshake_step.