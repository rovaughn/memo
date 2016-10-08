Require Export List.

Definition Map k v := list (k * v).

Fixpoint lookup {K V} (eq : K -> K -> bool) k (m : Map K V): option V :=
match m with
| nil => None
| cons (k', v') m' => if eq k k' then Some v' else lookup eq k m'
end.

Fixpoint insert {K V} (eq : K -> K -> bool) k v (m : Map K V): Map K V :=
match m with
| nil => cons (k, v) nil
| (k', v') :: m' =>
  if eq k k'
  then (k, v) :: m'
  else (k', v') :: insert eq k v m'
end.

Fixpoint map_all {K V} (f : K -> V -> bool) (m : Map K V): bool :=
match m with
| nil => true
| (k, v) :: m' => andb (f k v) (map_all f m')
end.

Fixpoint map_any {K V} (f : K -> V -> bool) (m : Map K V): bool :=
match m with
| nil => false
| (k, v) :: m' => orb (f k v) (map_any f m')
end.
