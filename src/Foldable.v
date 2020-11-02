Require Import List PeanoNat FunctionalExtensionality Inhabit.
Require String Ascii.
Import ListNotations.
Import String.StringSyntax.
Set Implicit Arguments.
Open Scope type_scope.
Open Scope string_scope.

Fixpoint zip_list A1 A2 (l1 : list A1)(l2 : list A2) : option (list (A1 * A2)):=
  match l1, l2 with
  | [], [] => Some []
  | a1::l1', a2::l2' =>
    option_map (fun l => (a1,a2) :: l) (zip_list l1' l2')
  | _, _ => None
  end.

Class Foldable (F : Set -> Set) :=
  { foldr : forall (A B : Set), (A -> B -> B) -> B -> F A -> B;
    zip : forall (A1 A2 : Set), F A1 -> F A2 -> option (F (A1 * A2));
    to_list : forall A:Set, F A -> list A;
    to_list_foldr : forall (A B:Set) (f : A -> B -> B) b x,
        foldr f b x = fold_right f b (to_list x);
    zip_to_list : forall (A1 A2 :Set)(x1 : F A1)(x2 : F A2) x,
        zip x1 x2 = Some x -> Some (to_list x) = zip_list (to_list x1) (to_list x2)
  }.

Program Instance list_Foldable : Foldable list :=
  { foldr := fun A B => @fold_right B A;
    zip := zip_list;
    to_list := fun _ x => x
  }.

Definition size A F `{F_Foldable : Foldable F} (x : F A) : (nat : Set) :=
  foldr (fun _ accum => S accum) 0 x.

Definition nth_err A F `{F_Foldable : Foldable F}(x : F A) :=
  foldr (fun a p n =>
           match n with
           | O => Some a
           | S n' => p n'
           end)
        (fun _ => None) x.

Fixpoint replace_list (A:Set) n a (l : list A):=
  match l with
  | [] => []
  | x::l' =>
    match n with
    | O => a::l'
    | S n' => x :: replace_list n' a l'
    end
  end.

Class HasGenForall2 (F : Set -> Set) :=
  { GenForall2 : forall (A1 A2 : Set), (A1 -> A2 -> Prop) -> F A1 -> F A2 -> Prop }.

Instance HasGenForall2_Foldable (F : Set -> Set) `{F_Foldable : Foldable F}
  : HasGenForall2 F :=
  { GenForall2 A1 A2 R x1 x2 :=
      exists x, zip _ _ x1 x2 = Some x /\ fold_right (fun '(a1,a2) p => R a1 a2 /\ p) True (to_list _ x) }.

(*
Definition GenForall2 (A1 A2:Set) (F: Set -> Set) `{F_Foldable : Foldable F}
           (R : A1 -> A2 -> Prop) (x1 : F A1) (x2 : F A2) :=
  exists x, zip _ _ x1 x2 = Some x /\ fold_right (fun '(a1, a2) (p:Prop) => R a1 a2 /\ p) True (to_list _ x).
*)

Lemma GenForall2_cons : forall (A1 A2 :Set)(R : A1 -> A2 -> Prop) (x1 : list A1) (x2 : list A2) a1 a2,
    R a1 a2 ->
    GenForall2 R x1 x2 ->
    GenForall2 R (a1::x1) (a2::x2).
Proof.
  unfold GenForall2. simpl.
  intros.
  destruct H0 as (x,(H1,H2)).
  exists ((a1,a2) :: x).
  split.
  rewrite H1.
  auto.
  simpl.
  auto.
Qed.
  

Lemma nth_err_nth_error : forall (A:Set) F (F_Foldable : Foldable F) (x : F A) n,
    nth_err _ x n = nth_error (to_list _ x) n.
Proof.
  intros.
  unfold nth_err.
  rewrite to_list_foldr.
  revert n.
  induction (to_list A x); intros; simpl.
  destruct n; auto.
  destruct n; simpl; auto.
Qed.

Lemma size_length : forall (A:Set) F (F_Foldable : Foldable F) (x : F A),
    size _ x = length (to_list _ x).
Proof.
  intros.
  unfold size.
  rewrite to_list_foldr.
  induction (to_list _ x); simpl; auto.
Qed.

Lemma nth_err_Some : forall (A:Set) (F : Set -> Set) (F_Foldable : Foldable F) (x : F A) n a,
    nth_err _ x n = Some a ->
    n < size _ x.
Proof.
  intros.
  unfold size, nth_err in *.
  rewrite to_list_foldr in *.
  revert n a H.
  induction (to_list _ x); simpl; intros.
  congruence.
  destruct n.
  auto with arith.
  apply -> PeanoNat.Nat.succ_lt_mono.
  eauto.
Qed.

Lemma nth_err_None : forall (A:Set) F (F_Foldable : Foldable F) (x : F A) n,
    nth_err _ x n = None ->
    ~ n < size _ x.
Proof.
  intros.
  unfold size, nth_err in *.
  rewrite to_list_foldr in *.
  revert n H.
  induction (to_list _ x); simpl; intros.
  auto with arith.
  destruct n.
  congruence.
  apply IHl in H.
  auto with arith.
Qed.

Lemma GenForall2_Forall2 : forall (A1 A2:Set) F (F_Foldable : Foldable F) R (x1 : F A1) (x2 : F A2),
    GenForall2 R x1 x2 -> Forall2 R (to_list _ x1) (to_list _ x2).
Proof.
  intros.
  unfold GenForall2 in H.
  destruct H as (x,(H0,H1)).
  apply zip_to_list in H0.
  generalize dependent (to_list _ x).
  generalize (to_list A2 x2).
  induction (to_list _ x1); intros.
  destruct l.
  auto.
  simpl in H0.
  congruence.
  destruct l0.
  simpl in H0.
  congruence.
  simpl in *.
  destruct (zip_list l l0) eqn:?.
  simpl in *.
  symmetry in Heqo.
  inversion H0. subst.
  simpl in H1.
  econstructor.
  tauto.
  apply IHl in Heqo.
  auto.
  tauto.
  simpl in H0.
  congruence.
Qed.

Lemma Forall2_GenForall2 : forall (A1 A2:Set) R (x1 : list A1) (x2 : list A2),
     Forall2 R x1 x2 -> GenForall2 R x1 x2.
Proof.
  intros.
  unfold GenForall2. simpl.
  induction H; simpl.
  exists []. simpl. auto.
  destruct IHForall2 as (l1,(H1,H2)).
  exists ((x,y)::l1); simpl.
  rewrite H1. simpl. auto.
Qed.
  
Lemma GenForall2_size : forall (A1 A2 : Set) (F : Set -> Set) (F_Foldable : Foldable F) R (x1 : F A1) (x2 : F A2),
    GenForall2 R x1 x2 ->
    size _ x1 = size _ x2.
Proof.
  intros.
  destruct H.
  destruct H.
  apply zip_to_list in H.
  unfold size.
  repeat rewrite to_list_foldr in *.
  generalize dependent (to_list _ x2).
  generalize dependent (to_list _ x).
  induction (to_list _ x1); simpl in *; intros.
  destruct l0; simpl in *; congruence.
  destruct l1; simpl in *.
  congruence.
  f_equal.
  destruct (zip_list l l1) eqn:?; simpl in *.
  apply (IHl l2).
  inversion H. subst.
  simpl in H0.
  tauto.
  inversion H. subst.
  auto.
  congruence.
Qed.

Lemma GenForall2_nth_Some_None : forall (A1 A2 : Set) R (x1 : list A1) (x2 : list A2) n a1,
    GenForall2 (F := list) R x1 x2 ->
    nth_err _ x1 n = Some a1 ->
    nth_err _ x2 n = None ->
    False.
Proof.
  intros.
  apply nth_err_None in H1.
  apply nth_err_Some in H0.
  apply GenForall2_size in H.
  rewrite H in H0.
  auto.
Qed.

Lemma GenForall2_nth_None_Some : forall (A1 A2 : Set) R (x1 : list A1) (x2 : list A2) n a2,
    GenForall2 (F := list) R x1 x2 ->
    nth_err _ x1 n = None ->
    nth_err _ x2 n = Some a2 ->
    False.
Proof.
  intros.
  apply nth_err_Some in H1.
  apply nth_err_None in H0.
  apply GenForall2_size in H.
  rewrite H in H0.
  auto.
Qed.

Lemma GenForall2_nth_Some : forall (A1 A2 : Set) (F : Set -> Set) (F_Foldable : Foldable F) R (x1 : F A1) (x2 : F A2) n a1 a2,
    GenForall2 R x1 x2 ->
    nth_err _ x1 n = Some a1 ->
    nth_err _ x2 n = Some a2 ->
    R a1 a2.
Proof.
  intros.
  unfold nth_err in *.
  unfold GenForall2 in H.
  destruct H.
  destruct H.
  unfold size in H.
  rewrite to_list_foldr in H0.
  rewrite to_list_foldr in H1.
  apply zip_to_list in H.
  generalize dependent (to_list _ x2).
  generalize dependent (to_list _ x).
  revert n a1 a2 H0.
  induction (to_list _ x1); simpl in *; intros.
  destruct l0.
  inversion H. subst.
  simpl in H1.
  congruence.
  congruence.
  destruct l1; [congruence|].
  destruct (zip_list l l1) eqn:?; simpl in *; [|congruence].
  inversion H. subst.
  simpl in H2.
  destruct n.
  inversion H0. subst.
  inversion H1. subst.
  tauto.
  destruct H2.
  eapply IHl.
  eauto.
  eauto.
  symmetry. eauto.
  auto.
Qed.

Lemma GenForall2_replace_list : forall (A1 A2:Set)(R : A1 -> A2 -> Prop)
                                       n a1 a2 l1 l2,
    R a1 a2 ->
    GenForall2 R l1 l2 ->
    GenForall2 R (replace_list n a1 l1) (replace_list n a2 l2).
Proof.
  intros.
  apply GenForall2_Forall2 in H0.
  apply Forall2_GenForall2.
  unfold to_list in *. simpl in *.
  revert n.
  induction H0; intros.
  destruct n; simpl; auto.
  destruct n; simpl.
  econstructor; auto.
  econstructor; auto.
Qed.
  
Hint Resolve GenForall2_size nth_err_None nth_err_Some GenForall2_cons GenForall2_nth_None_Some GenForall2_nth_Some_None GenForall2_replace_list : foldable.


Inductive Map A := Node : String.string * A -> Map A -> Map A -> Map A | Leaf.

Definition compareAscii (x y : Ascii.ascii) :=
  Nat.compare (Ascii.nat_of_ascii x) (Ascii.nat_of_ascii y).

Fixpoint compareString (x y : String.string) :=
  match x, y with
  | String.EmptyString, String.EmptyString => Eq
  | String.EmptyString, _ => Lt
  | _, String.EmptyString => Gt
  | String.String c x', String.String d y' =>
    match compareAscii c d with
    | Eq => compareString x' y'
    | Lt => Lt
    | Gt => Gt
    end
  end.

Definition lebString (x y : String.string) :=
  match compareString x y with
  | Gt => false
  | _ => true
  end.

Fixpoint insert A x a0 (t : Map A) :=
  match t with
  | Node (y,a) l r =>
    if lebString x y then
      Node (y,a) (insert x a0 l) r
    else
      Node (y,a) l (insert x a0 r)
  | Leaf _ =>
    Node (x,a0) (Leaf _) (Leaf _)
  end.

Fixpoint bsearch A key (t : Map A) :=
  match t with
  | Node (x,a) l r =>
    match compareString key x with
    | Eq => Some a
    | Lt => bsearch key l
    | Gt => bsearch key r
    end
  | Leaf _ => None
  end.

Fixpoint replace_map A key a0 (t : Map A) :=
  match t with
  | Node (x,a) l r =>
    match compareString key x with
    | Eq => Node (key,a0) l r
    | Lt => Node (x,a) (replace_map key a0 l) r
    | Gt => Node (x,a) l (replace_map key a0 r)
    end
  | Leaf _ => Leaf _
  end.

Fixpoint deleteHelper A node (l r : Map A) : (String.string * A) * Map A :=
  match l with
  | Leaf _ => (node, r)
  | Node node' l' r' =>
    let (n, new) := deleteHelper node' l' r' in
    (n, Node node new r)
  end.

Fixpoint delete A key (t : Map A) :=
    match t with
    | Leaf _ => Leaf _
    | Node (x,a) l r =>
      match compareString key x with
      | Eq =>
        match l,r with
        | Leaf _, Leaf _ => Leaf _
        | Leaf _, _ => r
        | _, Leaf _ => l
        | _, Node n l' r' =>
          let (node, newr) := deleteHelper n l' r' in
          Node node l newr
        end
      | Lt => Node (x,a) (delete key l) r
      | Gt => Node (x,a) l (delete key r)
      end
    end.

Fixpoint foldr_map (A B:Set) (f : A -> B -> B)(init : B)(t : Map A) :=
  match t with
  | Node (k,a) l r => foldr_map f (f a (foldr_map f init r)) l
  | Leaf _ => init
  end.

Fixpoint zip_map A1 A2 (m1 : Map A1)(m2 : Map A2) :=
  match m1, m2 with
  | Node (k1,a1) l1 r1, Node (k2,a2) l2 r2 =>
    if String.string_dec k1 k2 then
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

Definition from_map_to_list (A:Set) (t : Map A) :=
  foldr_map (fun a accum => a :: accum) [] t.

Lemma fold_right_cons_app : forall A (l l0 : list A),
    fold_right (fun a l' => a::l') l0 l = l ++ l0.
Proof.
  induction l; simpl; intros; congruence.
Qed.

Lemma to_list_foldr_map : forall (A B : Set) (f : A -> B -> B) (b : B) (x : Map A),
    foldr_map f b x = fold_right f b (from_map_to_list x).
Proof.
  intros.
  unfold from_map_to_list.
  revert B f b;
  induction x; simpl in *; intros.
  rewrite IHx2.
  destruct p.
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

Lemma zip_to_list_map : forall (A1 A2 : Set) (x1 : Map A1) (x2 : Map A2) (x : Map (A1 * A2)),
                  zip_map x1 x2 = Some x ->
                  Some (from_map_to_list x) =
                  zip_list (from_map_to_list x1) (from_map_to_list x2).
Proof.
  unfold from_map_to_list.
  intros.
  enough (forall l1 l2 l, zip_list l1 l2 = Some l ->
                          Some
    (foldr_map (fun (a : A1 * A2) (accum : list (A1 * A2)) => a :: accum) l x) =
  zip_list (foldr_map (fun (a : A1) (accum : list A1) => a :: accum) l1 x1)
    (foldr_map (fun (a : A2) (accum : list A2) => a :: accum) l2 x2)) by auto.
  revert x x2 H.
  induction x1; simpl in *; intros.
  destruct p.
  destruct x2; simpl in *; [|congruence].
  destruct p.
  destruct (String.string_dec s s0); [|congruence].
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

Instance map_Foldable : Foldable Map :=
  { foldr := foldr_map;
    zip := zip_map;
    to_list := from_map_to_list;
    to_list_foldr := to_list_foldr_map;
    zip_to_list := zip_to_list_map
  }.


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
  destruct p.
  destruct m2.
  destruct p.
  simpl in H1.
  destruct (compareString k s0) eqn:?.
  congruence.
  destruct (String.string_dec s s0); [|congruence].
  subst.
  rewrite Heqc in H0.
  destruct (zip_map m1_1 m2_1) eqn:?; [|congruence].
  eauto.
  destruct (String.string_dec s s0); [|congruence].
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
  destruct p.
  destruct m2; [|congruence].
  destruct p.
  destruct (String.string_dec s s0); [|congruence].
  subst.
  simpl in H1.
  destruct (compareString k s0) eqn:?.
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

Inductive Forall2_map (A1 A2:Set) (R : A1 -> A2 -> Prop) : Map A1 -> Map A2 -> Prop :=
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

Lemma fold_map_app : forall (A:Set) (t:Map A) (l : list A),
    foldr_map (fun (a : A) accum => a :: accum) l t
    = foldr_map (fun a accum => a :: accum) [] t ++ l.
Proof.
  induction t; simpl; intros.
  destruct p.
  rewrite IHt2.
  rewrite IHt1.
  setoid_rewrite IHt1 at 2.
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
  destruct p.
  destruct p0.
  destruct (String.string_dec s s0); [|congruence].
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
        (fun (a1 : A1 * A2) (accum : list (A1 * A2)) => a1 :: accum) [] m0))
    by intuition.
  revert H1.
  generalize ((a,a0) :: foldr_map (fun  (a1 : A1 * A2) (accum : list (A1 * A2)) => a1 :: accum) [] m0).
  clear H H0 Heqo.
  induction m; simpl; intros.
  destruct p.
  apply IHm1; simpl; auto.
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
  destruct p. congruence.
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
  destruct (String.string_dec k k); [|congruence].
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
  destruct (compareString k k0) eqn:?.
  inversion H0. subst.
  inversion H1. subst.
  auto.
  eauto.
  eauto.
  congruence.
Qed.

Lemma GenForall2_replace_map : forall (A B : Set)(R : A -> B -> Prop)(m1 : Map A) m2 a b n,
    GenForall2 R m1 m2 ->
    R a b ->
    GenForall2 R (replace_map n a m1) (replace_map n b m2).
Proof.
  intros.
  apply GenForall2_Forall2_map.
  apply GenForall2_Forall2_map in H.
  revert m2 a b n H H0.
  induction m1; intros.
  simpl.
  destruct p.
  inversion H. subst.
  simpl.
  destruct (compareString n s) eqn:?; constructor; auto.
  inversion H. subst.
  simpl.
  constructor.
Qed.

  Instance Map_inhabitant A : Inhabit (Map A) := { inhabitant := Leaf _ }.

Hint Resolve GenForall2_bsearch_Some_None GenForall2_bsearch_None_Some GenForall2_replace_map : foldable.
