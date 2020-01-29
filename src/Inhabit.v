Require String.

Class Inhabit A := { inhabitant : A }.

Definition dummy Idx A `{IA : Inhabit A} (i : Idx) : A := inhabitant.

Instance nat_inhabit : Inhabit nat := { inhabitant := 0 }.

Instance list_inhabit T : Inhabit (list T) := { inhabitant := @nil T }.

Instance unit_inhabitant : Inhabit unit := {inhabitant := tt }.

Instance prod_inhabitant A B `{IA : Inhabit A} `{IB : Inhabit B} : Inhabit (A * B) :=
  { inhabitant := (inhabitant, inhabitant) }.

Instance string_inhabitant : Inhabit String.string :=
  { inhabitant := String.EmptyString }.

Instance sum_inhabitant A B `{IA : Inhabit A} : Inhabit (A + B) :=
  { inhabitant := inl inhabitant }.

Instance arrow_inhabitant A B `{IB : Inhabit B} : Inhabit (A -> B) :=
  { inhabitant := fun _:A => inhabitant }.

Instance option_inhabitant A : Inhabit (option A) :=
  { inhabitant := None }.
Instance Set_inhabitant : Inhabit Set :=
  { inhabitant := unit }.

Instance Type_inhabitant : Inhabit Type :=
  { inhabitant := unit }.