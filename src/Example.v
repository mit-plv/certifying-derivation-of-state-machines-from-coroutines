Require Import Inhabit Foldable ClConv.

(** We consider two effectful operations, [GetRand] and [PutNum]. *)

Inductive my_eff := GetRand | PutNum.

(** Let's say that [GetRand] takes [unit] and [PutNum] takes [nat] as their arguments *)

Definition args_my_eff (e : my_eff) :=
  match e with
  | GetRand => unit
  | PutNum => nat
  end.

(** ... and [GetRand] returns [nat] and [PutNum] returns [unit]. *)
Definition rets_my_eff (e : my_eff) :=
  match e with
  | GetRand => nat
  | PutNum => unit
  end.

(** To help the compiler, we need: *)

Definition lift_my_eff A B
           (e : my_eff)(a : rets_my_eff e -> A + option B)(e0 : my_eff)
  : rets_my_eff e0 -> A + option B :=
  match e as e1
        return ((rets_my_eff e1 -> A + option B) -> rets_my_eff e0 -> A + option B)
  with
  | GetRand => 
    fun a0 : rets_my_eff GetRand -> A + option B =>
      match e0 as e1 return (rets_my_eff e1 -> A + option B) with
      | GetRand => a0
      | _ => fun _ => inr None
      end
  | PutNum => 
    fun a0 : rets_my_eff PutNum -> A + option B =>
      match e0 as e1 return (rets_my_eff e1 -> A + option B) with
      | PutNum => a0
      | _ => fun _ => inr None
      end
  end a.

Instance effect_is_eff : is_eff my_eff :=
  { args := args_my_eff;
    rets := rets_my_eff;
    lift_eff := lift_my_eff }.

(** If you add a constructor to [my_eff], you can simply add
[[[
| YourConstructr =>
    fun a0 : rets_my_eff YourConstructor -> A + option B =>
      match e0 as e1 return (rets_my_eff e1 -> A + option B) with
      | YourConstructor => a0
      | _ => fun _ => inr None
      end
]]]
as a branch.
*)

(** Introduce notations so that we can write programs in an imperative style. *)

Notation "x <- 'getRand' ; e" :=
  (Eff GetRand (tt : args_my_eff GetRand) (fun x : rets_my_eff GetRand => e))
    (at level 100, right associativity).

Notation "'putNum' n ; e" :=
  (Eff PutNum (n : args_my_eff PutNum) (fun _ => e))
    (at level 200).

Definition ex1 : t args_my_eff rets_my_eff (option unit) :=
  x <- getRand;
  putNum x;
  Return None.

(** We construct a state machine, which consists of a type of states, a step function, and an initial state, and at the same time, a proof that [ex1] is equivalent to the state machine.

Programs with no coroutine can be compiled with the [derive'] tactic. *)

Lemma ex1_derive :
  { state & { step & { init | @equiv _ _ _ _ state step init ex1 } } }.
Proof.
  do 3 eexists.
  derive' tt. (* The argument [tt] means that [ex1] has no parameters. *)
Defined.

(** We can print the type of states and the initial state. *)
Eval cbv [ex1_derive projT1] in projT1 ex1_derive.
Eval cbv [ex1_derive projT2 proj1_sig] in proj1_sig (projT2 (projT2 ex1_derive)).

(** The type of states is given as a sum type, and each component is the type of a single state.
We have four states for this state machine, and [inl tt] is the initial state. Print the compiled step function as well: *)

Eval cbv [ex1_derive projT1 projT2 sum_merge prod_curry lift_my_eff] in projT1 (projT2 ex1_derive).

(**
In the paper, we described a step function in more human readable like [add_coro] in Section 2, and this is the actual compiler's output.

The first branch
[[[
       | inl _ =>
           fun (e : my_eff) (_ : rets_my_eff e) => inl (inr (inl tt), Some (existT GetRand tt))
]]]
describes the transition from the initial state [inl _] to the next state [inr (inl tt)] and the next operation to run is [GetRand tt].
The second branch
[[[
       | inr (inl _) =>
           fun e0 : my_eff =>
           match
             e0 as e1
             return
               (rets_my_eff e1 ->
                (unit + (unit + (unit * nat + option unit))) *
                option {e : my_eff & args_my_eff e} + option unit)
           with
           | GetRand => fun r : nat => inl (inr (inr (inl (tt, r))), Some (existT PutNum r))
           | PutNum => fun _ : rets_my_eff PutNum => inr None
           end
]]]
looks a little complicated, but it means: At the state [inr (inl _)], if the previous effectful operation [e0] is [GetRand] and its result is [r], then go to the state [inr (inr (inl (tt, r)))].
If [e0] is [PutNum] (this is not supposed to be happened), go to the final state [inr None].
We can interpret the other branches in the same way.


*)


(** Let's define a simple child coroutine. *)

Definition coro_add (n s0:nat) : t (const_yield nat) (const_yield nat) unit :=
  s1 <- yield (n + s0)%nat;
  _ <- yield (s0 + s1)%nat;
  Return tt.

(** The child coroutine [coro_add] will be used as
[[[
let_coro c := coro_add n in
...
x <- resume c $ s0;
...
]]]
but we first compile it. We use the [derive_coro] to compile.
*)

Lemma coro_add_derive :
  { state & { step & forall n, { init | @equiv_coro _ _ _ _ _ state step init (coro_add n) }}}.
  do 3 eexists.
  unfold coro_add.
  unshelve derive_coro (tt, n); exact inhabitant.
  (* We pair parameters (in this case, [n]) of a program with [tt], and pass to [derive_coro] *)
Defined.

(** Then we have a step function. This corresponds to `ex_coro'` in the paper. *)

Definition coro_add_step :=
  projT1 (projT2 coro_add_derive).

(** We use the commands below to help our compiler. *)

Definition coro_add_equiv n : equiv_coro coro_add_step (inl (tt, n)) (coro_add n) :=
  proj2_sig (projT2 (projT2 coro_add_derive) n).
Hint Resolve coro_add_equiv : equivc.

(** Now let's define a simple parent: *)

Definition ex2 : t args_my_eff rets_my_eff (option unit) :=
  let_coro c : coro_type coro_add_step := coro_add 2 in
  x <- resume c $ 1;
  putNum x;
  y <- resume c $ 3;
  putNum y;
  Return None.

(** To help the compiler, we pass the step function [coro_add_step] of the child inside the type annotation.

We use the [derive] tactic to compile parents. *)

Lemma ex2_derive :
  { state & { step & { init | @equiv _ _ _ _ state step init ex2 } } }.
Proof.
  do 3 eexists.
  unshelve derive tt; exact inhabitant.
Defined.

Eval cbv [ex2_derive projT1 projT2 sum_merge prod_curry] in projT1 (projT2 ex2_derive).


(** Here is a parent with recursion. *)

Definition ex3 (fuel : nat) : t args_my_eff rets_my_eff (option unit) :=
  let_coro c : coro_type coro_add_step := coro_add 0 in
  nat_rect_nondep
    (fun _ => Return None)
    (fun _ rec n_c =>
       let (n, c) := n_c : nat * coro_type coro_add_step in
       putNum n;
       x <- resume c $ n;
       rec (x, c)
    )
    fuel (0, c).

(** Note that we pass the coroutine variable [c] to [nat_rect_nondep]. Otherwise, [resume] will invoke the first line of [coro_add] on every recursive call, and will never proceed to the next line (and our tactic does not expect such input). *)

Lemma ex3_derive:
  { state & { step & forall fuel, { init | @equiv _ _ _ _ state step init (ex3 fuel) } } }.
Proof.
  do 3 eexists.
  unshelve derive (tt, fuel); exact inhabitant.
Defined.
