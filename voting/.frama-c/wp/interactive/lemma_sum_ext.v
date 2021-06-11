(* This file is generated by Why3's Coq driver *)
(* Beware! Only edit allowed sections below    *)
Require Import BuiltIn.
Require BuiltIn.
Require HighOrd.
Require bool.Bool.
Require int.Int.
Require int.Abs.
Require int.ComputerDivision.
Require real.Real.
Require real.RealInfix.
Require real.FromInt.
Require map.Map.

Parameter eqb:
  forall {a:Type} {a_WT:WhyType a}, a -> a -> Init.Datatypes.bool.

Axiom eqb1 :
  forall {a:Type} {a_WT:WhyType a},
  forall (x:a) (y:a), ((eqb x y) = Init.Datatypes.true) <-> (x = y).

Axiom eqb_false :
  forall {a:Type} {a_WT:WhyType a},
  forall (x:a) (y:a), ((eqb x y) = Init.Datatypes.false) <-> ~ (x = y).

Parameter neqb:
  forall {a:Type} {a_WT:WhyType a}, a -> a -> Init.Datatypes.bool.

Axiom neqb1 :
  forall {a:Type} {a_WT:WhyType a},
  forall (x:a) (y:a), ((neqb x y) = Init.Datatypes.true) <-> ~ (x = y).

Parameter zlt: Numbers.BinNums.Z -> Numbers.BinNums.Z -> Init.Datatypes.bool.

Parameter zleq:
  Numbers.BinNums.Z -> Numbers.BinNums.Z -> Init.Datatypes.bool.

Axiom zlt1 :
  forall (x:Numbers.BinNums.Z) (y:Numbers.BinNums.Z),
  ((zlt x y) = Init.Datatypes.true) <-> (x < y)%Z.

Axiom zleq1 :
  forall (x:Numbers.BinNums.Z) (y:Numbers.BinNums.Z),
  ((zleq x y) = Init.Datatypes.true) <-> (x <= y)%Z.

Parameter rlt:
  Reals.Rdefinitions.R -> Reals.Rdefinitions.R -> Init.Datatypes.bool.

Parameter rleq:
  Reals.Rdefinitions.R -> Reals.Rdefinitions.R -> Init.Datatypes.bool.

Axiom rlt1 :
  forall (x:Reals.Rdefinitions.R) (y:Reals.Rdefinitions.R),
  ((rlt x y) = Init.Datatypes.true) <-> (x < y)%R.

Axiom rleq1 :
  forall (x:Reals.Rdefinitions.R) (y:Reals.Rdefinitions.R),
  ((rleq x y) = Init.Datatypes.true) <-> (x <= y)%R.

(* Why3 assumption *)
Definition real_of_int (x:Numbers.BinNums.Z) : Reals.Rdefinitions.R :=
  BuiltIn.IZR x.

Axiom c_euclidian :
  forall (n:Numbers.BinNums.Z) (d:Numbers.BinNums.Z), ~ (d = 0%Z) ->
  (n = (((ZArith.BinInt.Z.quot n d) * d)%Z + (ZArith.BinInt.Z.rem n d))%Z).

Axiom cmod_remainder :
  forall (n:Numbers.BinNums.Z) (d:Numbers.BinNums.Z),
  ((0%Z <= n)%Z -> (0%Z < d)%Z ->
   (0%Z <= (ZArith.BinInt.Z.rem n d))%Z /\ ((ZArith.BinInt.Z.rem n d) < d)%Z) /\
  ((n <= 0%Z)%Z -> (0%Z < d)%Z ->
   ((-d)%Z < (ZArith.BinInt.Z.rem n d))%Z /\
   ((ZArith.BinInt.Z.rem n d) <= 0%Z)%Z) /\
  ((0%Z <= n)%Z -> (d < 0%Z)%Z ->
   (0%Z <= (ZArith.BinInt.Z.rem n d))%Z /\
   ((ZArith.BinInt.Z.rem n d) < (-d)%Z)%Z) /\
  ((n <= 0%Z)%Z -> (d < 0%Z)%Z ->
   (d < (ZArith.BinInt.Z.rem n d))%Z /\ ((ZArith.BinInt.Z.rem n d) <= 0%Z)%Z).

Axiom cdiv_neutral :
  forall (a:Numbers.BinNums.Z), ((ZArith.BinInt.Z.quot a 1%Z) = a).

Axiom cdiv_inv :
  forall (a:Numbers.BinNums.Z), ~ (a = 0%Z) ->
  ((ZArith.BinInt.Z.quot a a) = 1%Z).

Axiom cdiv_closed_remainder :
  forall (a:Numbers.BinNums.Z) (b:Numbers.BinNums.Z) (n:Numbers.BinNums.Z),
  (0%Z <= a)%Z -> (0%Z <= b)%Z ->
  (0%Z <= (b - a)%Z)%Z /\ ((b - a)%Z < n)%Z ->
  ((ZArith.BinInt.Z.rem a n) = (ZArith.BinInt.Z.rem b n)) -> (a = b).

(* Why3 assumption *)
Inductive addr :=
  | addr'mk : Numbers.BinNums.Z -> Numbers.BinNums.Z -> addr.
Axiom addr_WhyType : WhyType addr.
Existing Instance addr_WhyType.

(* Why3 assumption *)
Definition offset (v:addr) : Numbers.BinNums.Z :=
  match v with
  | addr'mk x x1 => x1
  end.

(* Why3 assumption *)
Definition base (v:addr) : Numbers.BinNums.Z :=
  match v with
  | addr'mk x x1 => x
  end.

Parameter addr_le: addr -> addr -> Prop.

Parameter addr_lt: addr -> addr -> Prop.

Parameter addr_le_bool: addr -> addr -> Init.Datatypes.bool.

Parameter addr_lt_bool: addr -> addr -> Init.Datatypes.bool.

Axiom addr_le_def :
  forall (p:addr) (q:addr), ((base p) = (base q)) ->
  addr_le p q <-> ((offset p) <= (offset q))%Z.

Axiom addr_lt_def :
  forall (p:addr) (q:addr), ((base p) = (base q)) ->
  addr_lt p q <-> ((offset p) < (offset q))%Z.

Axiom addr_le_bool_def :
  forall (p:addr) (q:addr),
  addr_le p q <-> ((addr_le_bool p q) = Init.Datatypes.true).

Axiom addr_lt_bool_def :
  forall (p:addr) (q:addr),
  addr_lt p q <-> ((addr_lt_bool p q) = Init.Datatypes.true).

(* Why3 assumption *)
Definition null : addr := addr'mk 0%Z 0%Z.

(* Why3 assumption *)
Definition global (b:Numbers.BinNums.Z) : addr := addr'mk b 0%Z.

(* Why3 assumption *)
Definition shift (p:addr) (k:Numbers.BinNums.Z) : addr :=
  addr'mk (base p) ((offset p) + k)%Z.

(* Why3 assumption *)
Definition included (p:addr) (a:Numbers.BinNums.Z) (q:addr)
    (b:Numbers.BinNums.Z) : Prop :=
  (0%Z < a)%Z ->
  (0%Z <= b)%Z /\
  ((base p) = (base q)) /\
  ((offset q) <= (offset p))%Z /\
  (((offset p) + a)%Z <= ((offset q) + b)%Z)%Z.

(* Why3 assumption *)
Definition separated (p:addr) (a:Numbers.BinNums.Z) (q:addr)
    (b:Numbers.BinNums.Z) : Prop :=
  (a <= 0%Z)%Z \/
  (b <= 0%Z)%Z \/
  ~ ((base p) = (base q)) \/
  (((offset q) + b)%Z <= (offset p))%Z \/
  (((offset p) + a)%Z <= (offset q))%Z.

(* Why3 assumption *)
Definition eqmem {a:Type} {a_WT:WhyType a} (m1:addr -> a) (m2:addr -> a)
    (p:addr) (a1:Numbers.BinNums.Z) : Prop :=
  forall (q:addr), included q 1%Z p a1 -> ((m1 q) = (m2 q)).

Parameter havoc:
  forall {a:Type} {a_WT:WhyType a}, (addr -> a) -> (addr -> a) -> addr ->
  Numbers.BinNums.Z -> addr -> a.

(* Why3 assumption *)
Definition valid_rw (m:Numbers.BinNums.Z -> Numbers.BinNums.Z) (p:addr)
    (n:Numbers.BinNums.Z) : Prop :=
  (0%Z < n)%Z ->
  (0%Z < (base p))%Z /\
  (0%Z <= (offset p))%Z /\ (((offset p) + n)%Z <= (m (base p)))%Z.

(* Why3 assumption *)
Definition valid_rd (m:Numbers.BinNums.Z -> Numbers.BinNums.Z) (p:addr)
    (n:Numbers.BinNums.Z) : Prop :=
  (0%Z < n)%Z ->
  ~ (0%Z = (base p)) /\
  (0%Z <= (offset p))%Z /\ (((offset p) + n)%Z <= (m (base p)))%Z.

(* Why3 assumption *)
Definition valid_obj (m:Numbers.BinNums.Z -> Numbers.BinNums.Z) (p:addr)
    (n:Numbers.BinNums.Z) : Prop :=
  (0%Z < n)%Z ->
  (p = null) \/
  ~ (0%Z = (base p)) /\
  (0%Z <= (offset p))%Z /\ (((offset p) + n)%Z <= (1%Z + (m (base p)))%Z)%Z.

(* Why3 assumption *)
Definition invalid (m:Numbers.BinNums.Z -> Numbers.BinNums.Z) (p:addr)
    (n:Numbers.BinNums.Z) : Prop :=
  (n <= 0%Z)%Z \/
  ((base p) = 0%Z) \/
  ((m (base p)) <= (offset p))%Z \/ (((offset p) + n)%Z <= 0%Z)%Z.

Axiom valid_rw_rd :
  forall (m:Numbers.BinNums.Z -> Numbers.BinNums.Z), forall (p:addr),
  forall (n:Numbers.BinNums.Z), valid_rw m p n -> valid_rd m p n.

Axiom valid_string :
  forall (m:Numbers.BinNums.Z -> Numbers.BinNums.Z), forall (p:addr),
  ((base p) < 0%Z)%Z ->
  (0%Z <= (offset p))%Z /\ ((offset p) < (m (base p)))%Z ->
  valid_rd m p 1%Z /\ ~ valid_rw m p 1%Z.

Axiom separated_1 :
  forall (p:addr) (q:addr),
  forall (a:Numbers.BinNums.Z) (b:Numbers.BinNums.Z) (i:Numbers.BinNums.Z)
    (j:Numbers.BinNums.Z),
  separated p a q b -> ((offset p) <= i)%Z /\ (i < ((offset p) + a)%Z)%Z ->
  ((offset q) <= j)%Z /\ (j < ((offset q) + b)%Z)%Z ->
  ~ ((addr'mk (base p) i) = (addr'mk (base q) j)).

Parameter region: Numbers.BinNums.Z -> Numbers.BinNums.Z.

Parameter linked: (Numbers.BinNums.Z -> Numbers.BinNums.Z) -> Prop.

Parameter sconst: (addr -> Numbers.BinNums.Z) -> Prop.

(* Why3 assumption *)
Definition framed (m:addr -> addr) : Prop :=
  forall (p:addr), ((region (base (m p))) <= 0%Z)%Z.

Axiom separated_included :
  forall (p:addr) (q:addr),
  forall (a:Numbers.BinNums.Z) (b:Numbers.BinNums.Z), (0%Z < a)%Z ->
  (0%Z < b)%Z -> separated p a q b -> ~ included p a q b.

Axiom included_trans :
  forall (p:addr) (q:addr) (r:addr),
  forall (a:Numbers.BinNums.Z) (b:Numbers.BinNums.Z) (c:Numbers.BinNums.Z),
  included p a q b -> included q b r c -> included p a r c.

Axiom separated_trans :
  forall (p:addr) (q:addr) (r:addr),
  forall (a:Numbers.BinNums.Z) (b:Numbers.BinNums.Z) (c:Numbers.BinNums.Z),
  included p a q b -> separated q b r c -> separated p a r c.

Axiom separated_sym :
  forall (p:addr) (q:addr),
  forall (a:Numbers.BinNums.Z) (b:Numbers.BinNums.Z),
  separated p a q b <-> separated q b p a.

Axiom eqmem_included :
  forall {a:Type} {a_WT:WhyType a},
  forall (m1:addr -> a) (m2:addr -> a), forall (p:addr) (q:addr),
  forall (a1:Numbers.BinNums.Z) (b:Numbers.BinNums.Z), included p a1 q b ->
  eqmem m1 m2 q b -> eqmem m1 m2 p a1.

Axiom eqmem_sym :
  forall {a:Type} {a_WT:WhyType a},
  forall (m1:addr -> a) (m2:addr -> a), forall (p:addr),
  forall (a1:Numbers.BinNums.Z), eqmem m1 m2 p a1 -> eqmem m2 m1 p a1.

Axiom havoc_access :
  forall {a:Type} {a_WT:WhyType a},
  forall (m0:addr -> a) (m1:addr -> a), forall (q:addr) (p:addr),
  forall (a1:Numbers.BinNums.Z),
  (separated q 1%Z p a1 -> ((havoc m0 m1 p a1 q) = (m1 q))) /\
  (~ separated q 1%Z p a1 -> ((havoc m0 m1 p a1 q) = (m0 q))).

Parameter cinits: (addr -> Init.Datatypes.bool) -> Prop.

(* Why3 assumption *)
Definition is_init_range (m:addr -> Init.Datatypes.bool) (p:addr)
    (l:Numbers.BinNums.Z) : Prop :=
  forall (i:Numbers.BinNums.Z), (0%Z <= i)%Z /\ (i < l)%Z ->
  ((m (shift p i)) = Init.Datatypes.true).

Parameter set_init:
  (addr -> Init.Datatypes.bool) -> addr -> Numbers.BinNums.Z ->
  addr -> Init.Datatypes.bool.

Axiom set_init_access :
  forall (m:addr -> Init.Datatypes.bool), forall (q:addr) (p:addr),
  forall (a:Numbers.BinNums.Z),
  (separated q 1%Z p a -> ((set_init m p a q) = (m q))) /\
  (~ separated q 1%Z p a -> ((set_init m p a q) = Init.Datatypes.true)).

(* Why3 assumption *)
Definition monotonic_init (m1:addr -> Init.Datatypes.bool)
    (m2:addr -> Init.Datatypes.bool) : Prop :=
  forall (p:addr), ((m1 p) = Init.Datatypes.true) ->
  ((m2 p) = Init.Datatypes.true).

Parameter int_of_addr: addr -> Numbers.BinNums.Z.

Parameter addr_of_int: Numbers.BinNums.Z -> addr.

Axiom table : Type.
Parameter table_WhyType : WhyType table.
Existing Instance table_WhyType.

Parameter table_of_base: Numbers.BinNums.Z -> table.

Parameter table_to_offset: table -> Numbers.BinNums.Z -> Numbers.BinNums.Z.

Axiom table_to_offset_zero :
  forall (t:table), ((table_to_offset t 0%Z) = 0%Z).

Axiom table_to_offset_monotonic :
  forall (t:table), forall (o1:Numbers.BinNums.Z) (o2:Numbers.BinNums.Z),
  (o1 <= o2)%Z <-> ((table_to_offset t o1) <= (table_to_offset t o2))%Z.

Axiom int_of_addr_bijection :
  forall (a:Numbers.BinNums.Z), ((int_of_addr (addr_of_int a)) = a).

Axiom addr_of_int_bijection :
  forall (p:addr), ((addr_of_int (int_of_addr p)) = p).

Axiom addr_of_null : ((int_of_addr null) = 0%Z).

(* Why3 assumption *)
Definition is_bool (x:Numbers.BinNums.Z) : Prop := (x = 0%Z) \/ (x = 1%Z).

(* Why3 assumption *)
Definition is_uint8 (x:Numbers.BinNums.Z) : Prop :=
  (0%Z <= x)%Z /\ (x < 256%Z)%Z.

(* Why3 assumption *)
Definition is_sint8 (x:Numbers.BinNums.Z) : Prop :=
  ((-128%Z)%Z <= x)%Z /\ (x < 128%Z)%Z.

(* Why3 assumption *)
Definition is_uint16 (x:Numbers.BinNums.Z) : Prop :=
  (0%Z <= x)%Z /\ (x < 65536%Z)%Z.

(* Why3 assumption *)
Definition is_sint16 (x:Numbers.BinNums.Z) : Prop :=
  ((-32768%Z)%Z <= x)%Z /\ (x < 32768%Z)%Z.

(* Why3 assumption *)
Definition is_uint32 (x:Numbers.BinNums.Z) : Prop :=
  (0%Z <= x)%Z /\ (x < 4294967296%Z)%Z.

(* Why3 assumption *)
Definition is_sint32 (x:Numbers.BinNums.Z) : Prop :=
  ((-2147483648%Z)%Z <= x)%Z /\ (x < 2147483648%Z)%Z.

(* Why3 assumption *)
Definition is_uint64 (x:Numbers.BinNums.Z) : Prop :=
  (0%Z <= x)%Z /\ (x < 18446744073709551616%Z)%Z.

(* Why3 assumption *)
Definition is_sint64 (x:Numbers.BinNums.Z) : Prop :=
  ((-9223372036854775808%Z)%Z <= x)%Z /\ (x < 9223372036854775808%Z)%Z.

Axiom is_bool0 : is_bool 0%Z.

Axiom is_bool1 : is_bool 1%Z.

Parameter to_bool: Numbers.BinNums.Z -> Numbers.BinNums.Z.

Axiom to_bool'def :
  forall (x:Numbers.BinNums.Z),
  ((x = 0%Z) -> ((to_bool x) = 0%Z)) /\ (~ (x = 0%Z) -> ((to_bool x) = 1%Z)).

Parameter to_uint8: Numbers.BinNums.Z -> Numbers.BinNums.Z.

Parameter to_sint8: Numbers.BinNums.Z -> Numbers.BinNums.Z.

Parameter to_uint16: Numbers.BinNums.Z -> Numbers.BinNums.Z.

Parameter to_sint16: Numbers.BinNums.Z -> Numbers.BinNums.Z.

Parameter to_uint32: Numbers.BinNums.Z -> Numbers.BinNums.Z.

Parameter to_sint32: Numbers.BinNums.Z -> Numbers.BinNums.Z.

Parameter to_uint64: Numbers.BinNums.Z -> Numbers.BinNums.Z.

Parameter to_sint64: Numbers.BinNums.Z -> Numbers.BinNums.Z.

Parameter two_power_abs: Numbers.BinNums.Z -> Numbers.BinNums.Z.

Axiom two_power_abs_is_positive :
  forall (n:Numbers.BinNums.Z), (0%Z < (two_power_abs n))%Z.

Axiom two_power_abs_plus_pos :
  forall (n:Numbers.BinNums.Z) (m:Numbers.BinNums.Z), (0%Z <= n)%Z ->
  (0%Z <= m)%Z ->
  ((two_power_abs (n + m)%Z) = ((two_power_abs n) * (two_power_abs m))%Z).

Axiom two_power_abs_plus_one :
  forall (n:Numbers.BinNums.Z), (0%Z <= n)%Z ->
  ((two_power_abs (n + 1%Z)%Z) = (2%Z * (two_power_abs n))%Z).

(* Why3 assumption *)
Definition is_uint (n:Numbers.BinNums.Z) (x:Numbers.BinNums.Z) : Prop :=
  (0%Z <= x)%Z /\ (x < (two_power_abs n))%Z.

(* Why3 assumption *)
Definition is_sint (n:Numbers.BinNums.Z) (x:Numbers.BinNums.Z) : Prop :=
  ((-(two_power_abs n))%Z <= x)%Z /\ (x < (two_power_abs n))%Z.

Parameter to_uint:
  Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z.

Parameter to_sint:
  Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z.

Axiom is_to_uint :
  forall (n:Numbers.BinNums.Z) (x:Numbers.BinNums.Z), is_uint n (to_uint n x).

Axiom is_to_sint :
  forall (n:Numbers.BinNums.Z) (x:Numbers.BinNums.Z), is_sint n (to_sint n x).

Axiom is_to_uint8 : forall (x:Numbers.BinNums.Z), is_uint8 (to_uint8 x).

Axiom is_to_sint8 : forall (x:Numbers.BinNums.Z), is_sint8 (to_sint8 x).

Axiom is_to_uint16 : forall (x:Numbers.BinNums.Z), is_uint16 (to_uint16 x).

Axiom is_to_sint16 : forall (x:Numbers.BinNums.Z), is_sint16 (to_sint16 x).

Axiom is_to_uint32 : forall (x:Numbers.BinNums.Z), is_uint32 (to_uint32 x).

Axiom is_to_sint32 : forall (x:Numbers.BinNums.Z), is_sint32 (to_sint32 x).

Axiom is_to_uint64 : forall (x:Numbers.BinNums.Z), is_uint64 (to_uint64 x).

Axiom is_to_sint64 : forall (x:Numbers.BinNums.Z), is_sint64 (to_sint64 x).

Axiom id_uint :
  forall (n:Numbers.BinNums.Z) (x:Numbers.BinNums.Z),
  is_uint n x <-> ((to_uint n x) = x).

Axiom id_sint :
  forall (n:Numbers.BinNums.Z) (x:Numbers.BinNums.Z),
  is_sint n x <-> ((to_sint n x) = x).

Axiom id_uint8 :
  forall (x:Numbers.BinNums.Z), is_uint8 x -> ((to_uint8 x) = x).

Axiom id_sint8 :
  forall (x:Numbers.BinNums.Z), is_sint8 x -> ((to_sint8 x) = x).

Axiom id_uint16 :
  forall (x:Numbers.BinNums.Z), is_uint16 x -> ((to_uint16 x) = x).

Axiom id_sint16 :
  forall (x:Numbers.BinNums.Z), is_sint16 x -> ((to_sint16 x) = x).

Axiom id_uint32 :
  forall (x:Numbers.BinNums.Z), is_uint32 x -> ((to_uint32 x) = x).

Axiom id_sint32 :
  forall (x:Numbers.BinNums.Z), is_sint32 x -> ((to_sint32 x) = x).

Axiom id_uint64 :
  forall (x:Numbers.BinNums.Z), is_uint64 x -> ((to_uint64 x) = x).

Axiom id_sint64 :
  forall (x:Numbers.BinNums.Z), is_sint64 x -> ((to_sint64 x) = x).

Axiom proj_uint :
  forall (n:Numbers.BinNums.Z) (x:Numbers.BinNums.Z),
  ((to_uint n (to_uint n x)) = (to_uint n x)).

Axiom proj_sint :
  forall (n:Numbers.BinNums.Z) (x:Numbers.BinNums.Z),
  ((to_sint n (to_sint n x)) = (to_sint n x)).

Axiom proj_uint8 :
  forall (x:Numbers.BinNums.Z), ((to_uint8 (to_uint8 x)) = (to_uint8 x)).

Axiom proj_sint8 :
  forall (x:Numbers.BinNums.Z), ((to_sint8 (to_sint8 x)) = (to_sint8 x)).

Axiom proj_uint16 :
  forall (x:Numbers.BinNums.Z), ((to_uint16 (to_uint16 x)) = (to_uint16 x)).

Axiom proj_sint16 :
  forall (x:Numbers.BinNums.Z), ((to_sint16 (to_sint16 x)) = (to_sint16 x)).

Axiom proj_uint32 :
  forall (x:Numbers.BinNums.Z), ((to_uint32 (to_uint32 x)) = (to_uint32 x)).

Axiom proj_sint32 :
  forall (x:Numbers.BinNums.Z), ((to_sint32 (to_sint32 x)) = (to_sint32 x)).

Axiom proj_uint64 :
  forall (x:Numbers.BinNums.Z), ((to_uint64 (to_uint64 x)) = (to_uint64 x)).

Axiom proj_sint64 :
  forall (x:Numbers.BinNums.Z), ((to_sint64 (to_sint64 x)) = (to_sint64 x)).

Axiom proj_su :
  forall (n:Numbers.BinNums.Z) (x:Numbers.BinNums.Z),
  ((to_sint n (to_uint n x)) = (to_uint n x)).

Axiom incl_su :
  forall (n:Numbers.BinNums.Z) (x:Numbers.BinNums.Z), is_uint n x ->
  is_sint n x.

Axiom proj_su_uint :
  forall (n:Numbers.BinNums.Z) (m:Numbers.BinNums.Z) (x:Numbers.BinNums.Z),
  (0%Z <= n)%Z -> (0%Z <= m)%Z ->
  ((to_sint (m + n)%Z (to_uint n x)) = (to_uint n x)).

Axiom proj_su_sint :
  forall (n:Numbers.BinNums.Z) (m:Numbers.BinNums.Z) (x:Numbers.BinNums.Z),
  (0%Z <= n)%Z -> (0%Z <= m)%Z ->
  ((to_sint n (to_uint (m + (n + 1%Z)%Z)%Z x)) = (to_sint n x)).

Axiom proj_int8 :
  forall (x:Numbers.BinNums.Z), ((to_sint8 (to_uint8 x)) = (to_sint8 x)).

Axiom proj_int16 :
  forall (x:Numbers.BinNums.Z), ((to_sint16 (to_uint16 x)) = (to_sint16 x)).

Axiom proj_int32 :
  forall (x:Numbers.BinNums.Z), ((to_sint32 (to_uint32 x)) = (to_sint32 x)).

Axiom proj_int64 :
  forall (x:Numbers.BinNums.Z), ((to_sint64 (to_uint64 x)) = (to_sint64 x)).

Axiom proj_us_uint :
  forall (n:Numbers.BinNums.Z) (m:Numbers.BinNums.Z) (x:Numbers.BinNums.Z),
  (0%Z <= n)%Z -> (0%Z <= m)%Z ->
  ((to_uint (n + 1%Z)%Z (to_sint (m + n)%Z x)) = (to_uint (n + 1%Z)%Z x)).

Axiom incl_uint :
  forall (n:Numbers.BinNums.Z) (x:Numbers.BinNums.Z) (i:Numbers.BinNums.Z),
  (0%Z <= n)%Z -> (0%Z <= i)%Z -> is_uint n x -> is_uint (n + i)%Z x.

Axiom incl_sint :
  forall (n:Numbers.BinNums.Z) (x:Numbers.BinNums.Z) (i:Numbers.BinNums.Z),
  (0%Z <= n)%Z -> (0%Z <= i)%Z -> is_sint n x -> is_sint (n + i)%Z x.

Axiom incl_int :
  forall (n:Numbers.BinNums.Z) (x:Numbers.BinNums.Z) (i:Numbers.BinNums.Z),
  (0%Z <= n)%Z -> (0%Z <= i)%Z -> is_uint n x -> is_sint (n + i)%Z x.

(* Why3 assumption *)
Definition is_sint32_chunk (m:addr -> Numbers.BinNums.Z) : Prop :=
  forall (a:addr), is_sint32 (m a).

Parameter L_sum:
  (addr -> addr) -> (addr -> Numbers.BinNums.Z) -> addr ->
  Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z ->
  Numbers.BinNums.Z.

Axiom Q_sum1 :
  forall (Mptr:addr -> addr) (Mint:addr -> Numbers.BinNums.Z) (t:addr)
    (i:Numbers.BinNums.Z) (j:Numbers.BinNums.Z) (c:Numbers.BinNums.Z),
  (j <= i)%Z -> is_sint32_chunk Mint -> ((L_sum Mptr Mint t i j c) = 0%Z).

Axiom Q_sum2 :
  forall (Mptr:addr -> addr) (Mint:addr -> Numbers.BinNums.Z) (t:addr)
    (i:Numbers.BinNums.Z) (j:Numbers.BinNums.Z) (c:Numbers.BinNums.Z),
  let x := Mint (shift (Mptr (shift t j)) c) in
  (i <= j)%Z -> is_sint32_chunk Mint -> is_sint32 x ->
  (((L_sum Mptr Mint t i j c) + x)%Z = (L_sum Mptr Mint t i (1%Z + j)%Z c)).

Axiom Q_sum_4 :
  forall (Mptr:addr -> addr) (Mint:addr -> Numbers.BinNums.Z)
    (Mptr1:addr -> addr) (Mint1:addr -> Numbers.BinNums.Z) (t1:addr)
    (t2:addr) (i:Numbers.BinNums.Z) (j:Numbers.BinNums.Z)
    (c:Numbers.BinNums.Z),
  is_sint32_chunk Mint -> is_sint32_chunk Mint1 ->
  (forall (i1:Numbers.BinNums.Z), (i <= i1)%Z -> (i1 < j)%Z ->
   ((Mint1 (shift (Mptr1 (shift t1 i1)) c)) =
    (Mint (shift (Mptr (shift t2 i1)) c)))) ->
  ((L_sum Mptr1 Mint1 t1 i j c) = (L_sum Mptr Mint t2 i j c)).

Axiom Q_sum3 :
  forall (Mptr:addr -> addr) (Mint:addr -> Numbers.BinNums.Z) (t:addr)
    (i:Numbers.BinNums.Z) (j:Numbers.BinNums.Z) (k:Numbers.BinNums.Z)
    (c:Numbers.BinNums.Z),
  (0%Z <= i)%Z -> (i <= j)%Z -> (j <= k)%Z -> is_sint32_chunk Mint ->
  (((L_sum Mptr Mint t i j c) + (L_sum Mptr Mint t j k c))%Z =
   (L_sum Mptr Mint t i k c)).

(* Why3 assumption *)
Definition P_same_array (Mint:addr -> Numbers.BinNums.Z)
    (Mint1:addr -> Numbers.BinNums.Z) (a:addr) (b:addr)
    (begin:Numbers.BinNums.Z) (end1:Numbers.BinNums.Z) : Prop :=
  forall (i:Numbers.BinNums.Z), (begin <= i)%Z -> (i < end1)%Z ->
  ((Mint1 (shift a i)) = (Mint (shift b i))).

(* Why3 assumption *)
Definition P_same_array_e (Mptr:addr -> addr)
    (Mint:addr -> Numbers.BinNums.Z) (Mptr1:addr -> addr)
    (Mint1:addr -> Numbers.BinNums.Z) (a:addr) (b:addr)
    (begin:Numbers.BinNums.Z) (end1:Numbers.BinNums.Z)
    (count:Numbers.BinNums.Z) : Prop :=
  forall (i:Numbers.BinNums.Z), (begin <= i)%Z -> (i < end1)%Z ->
  P_same_array Mint Mint1 (Mptr1 (shift a i)) (Mptr (shift b i)) 0%Z count.

(* Why3 assumption *)
Definition P_swap (Mptr:addr -> addr) (Mint:addr -> Numbers.BinNums.Z)
    (Mptr1:addr -> addr) (Mint1:addr -> Numbers.BinNums.Z) (a:addr) (b:addr)
    (begin:Numbers.BinNums.Z) (i:Numbers.BinNums.Z) (j:Numbers.BinNums.Z)
    (end1:Numbers.BinNums.Z) (count:Numbers.BinNums.Z) : Prop :=
  ((((((begin <= i)%Z /\ (i < end1)%Z) /\ (begin <= j)%Z) /\ (j < end1)%Z) /\
    P_same_array Mint Mint1 (Mptr1 (shift a i)) (Mptr (shift b j)) 0%Z count) /\
   P_same_array Mint Mint1 (Mptr1 (shift a j)) (Mptr (shift b i)) 0%Z count) /\
  (forall (i1:Numbers.BinNums.Z), ~ (i1 = i) -> ~ (j = i1) ->
   (begin <= i1)%Z -> (i1 < end1)%Z ->
   P_same_array Mint Mint1 (Mptr1 (shift a i1)) (Mptr (shift b i1)) 0%Z count).

(* Why3 assumption *)
Inductive P_same_elements: (addr -> addr) -> (addr -> addr) ->
  (addr -> Numbers.BinNums.Z) -> (addr -> Numbers.BinNums.Z) -> addr ->
  addr -> Numbers.BinNums.Z -> Numbers.BinNums.Z -> Numbers.BinNums.Z ->
  Prop :=
  | Q_refl :
      forall (Mptr:addr -> addr) (Mint:addr -> Numbers.BinNums.Z)
        (Mptr1:addr -> addr) (Mint1:addr -> Numbers.BinNums.Z) (a:addr)
        (b:addr) (begin:Numbers.BinNums.Z) (end1:Numbers.BinNums.Z)
        (count:Numbers.BinNums.Z),
      is_sint32_chunk Mint -> is_sint32_chunk Mint1 ->
      P_same_array_e Mptr Mint Mptr1 Mint1 a b begin end1 count ->
      P_same_elements Mptr Mptr1 Mint Mint1 a b begin end1 count
  | Q_swap :
      forall (Mptr:addr -> addr) (Mint:addr -> Numbers.BinNums.Z)
        (Mptr1:addr -> addr) (Mint1:addr -> Numbers.BinNums.Z) (a:addr)
        (b:addr) (begin:Numbers.BinNums.Z) (i:Numbers.BinNums.Z)
        (j:Numbers.BinNums.Z) (end1:Numbers.BinNums.Z)
        (count:Numbers.BinNums.Z),
      is_sint32_chunk Mint -> is_sint32_chunk Mint1 ->
      P_swap Mptr Mint Mptr1 Mint1 a b begin i j end1 count ->
      P_same_elements Mptr Mptr1 Mint Mint1 a b begin end1 count
  | Q_trans :
      forall (Mptr:addr -> addr) (Mint:addr -> Numbers.BinNums.Z)
        (Mptr1:addr -> addr) (Mint1:addr -> Numbers.BinNums.Z)
        (Mptr2:addr -> addr) (Mint2:addr -> Numbers.BinNums.Z) (a:addr)
        (b:addr) (c:addr) (begin:Numbers.BinNums.Z) (end1:Numbers.BinNums.Z)
        (count:Numbers.BinNums.Z),
      is_sint32_chunk Mint -> is_sint32_chunk Mint2 ->
      is_sint32_chunk Mint1 ->
      P_same_elements Mptr Mptr1 Mint Mint1 b c begin end1 count ->
      P_same_elements Mptr1 Mptr2 Mint1 Mint2 a b begin end1 count ->
      P_same_elements Mptr Mptr2 Mint Mint2 a c begin end1 count.

(* Why3 goal *)
Theorem wp_goal :
  forall (t:addr -> addr) (t1:addr -> Numbers.BinNums.Z) (t2:addr -> addr)
    (t3:addr -> Numbers.BinNums.Z) (a:addr) (a1:addr) (i:Numbers.BinNums.Z)
    (i1:Numbers.BinNums.Z) (i2:Numbers.BinNums.Z) (i3:Numbers.BinNums.Z),
  (0%Z <= i2)%Z -> (i2 < i3)%Z -> (i <= i1)%Z -> (0%Z <= i)%Z ->
  is_sint32_chunk t3 -> is_sint32_chunk t1 ->
  P_same_elements t t2 t1 t3 a a1 i i1 i3 ->
  ((L_sum t2 t3 a i i1 i2) = (L_sum t t1 a1 i i1 i2)).
Proof.
intros.
induction H5.
* apply Q_sum_4; [ assumption | assumption | ].
  intros.
  unfold P_same_array_e in H7.
  unfold P_same_array in H7.
  apply H7.
  all: try assumption.
* unfold P_swap in H7.
  destruct H7.
  destruct H7.
  destruct H7.
  unfold P_same_array in H8.
  Search ( _ < _ \/ _)%Z.
  destruct (Z.lt_total i j).
  + rewrite <- (Q_sum3 Mptr1 Mint1 a begin i end1 i2) by auto with zarith.
    rewrite <- (Q_sum3 Mptr Mint b begin i end1 i2) by auto with zarith.

    apply Zplus_eq_compat.
    apply Q_sum_4.
    all:auto with zarith.

    rewrite <- (Q_sum3 Mptr1 Mint1 a i (1 + i) end1 i2) by auto with zarith.
    rewrite <- (Q_sum3 Mptr Mint b i (1 + i) end1 i2) by auto with zarith.

    rewrite <- (Q_sum3 Mptr1 Mint1 a (1 + i) j end1 i2) by auto with zarith.
    rewrite <- (Q_sum3 Mptr Mint b (1 + i) j end1 i2) by auto with zarith.

    rewrite (Z.add_shuffle3 (L_sum Mptr Mint b i (1 + i) i2)).
    rewrite Z.add_shuffle3.
    apply Zplus_eq_compat.
    apply Q_sum_4.
    all:auto with zarith.

    rewrite <- (Q_sum3 Mptr1 Mint1 a j (1 + j) end1 i2) by auto with zarith.
    rewrite <- (Q_sum3 Mptr Mint b j (1 + j) end1 i2) by auto with zarith.

    rewrite (Z.add_shuffle3 (L_sum Mptr Mint b i (1 + i) i2 )).
    apply Zplus_eq_compat.
    rewrite <- Q_sum2 by auto with zarith.
    rewrite <- Q_sum2 by auto with zarith.
    rewrite Q_sum1 by auto with zarith.
    rewrite Q_sum1 by auto with zarith.
    simpl.
    unfold P_same_array in H10.
    rewrite H10 by auto with zarith.
    reflexivity.

    apply Zplus_eq_compat.
    rewrite <- Q_sum2 by auto with zarith.
    rewrite <- Q_sum2 by auto with zarith.
    rewrite Q_sum1 by auto with zarith.
    rewrite Q_sum1 by auto with zarith.
    simpl.
    unfold P_same_array in H9.
    rewrite H9 by auto with zarith.
    reflexivity.

    apply Q_sum_4.
    all:auto with zarith.
  + destruct H11.
    - rewrite <- (Q_sum3 Mptr1 Mint1 a begin i end1 i2) by auto with zarith.
    rewrite <- (Q_sum3 Mptr Mint b begin i end1 i2) by auto with zarith.

    apply Zplus_eq_compat.
    apply Q_sum_4.
    all:auto with zarith.

    rewrite <- (Q_sum3 Mptr1 Mint1 a i (1 + i) end1 i2) by auto with zarith.
    rewrite <- (Q_sum3 Mptr Mint b i (1 + i) end1 i2) by auto with zarith.

    apply Zplus_eq_compat.
    rewrite <- Q_sum2 by auto with zarith.
    rewrite <- Q_sum2 by auto with zarith.
    rewrite Q_sum1 by auto with zarith.
    rewrite Q_sum1 by auto with zarith.
    simpl.
    unfold P_same_array in H10.
    rewrite H10 by auto with zarith.
    rewrite H11.
    reflexivity.
 
    apply Q_sum_4.
    all:auto with zarith.
  - rewrite <- (Q_sum3 Mptr1 Mint1 a begin j end1 i2) by auto with zarith.
    rewrite <- (Q_sum3 Mptr Mint b begin j end1 i2) by auto with zarith.

    apply Zplus_eq_compat.
    apply Q_sum_4.
    all:auto with zarith.

    rewrite <- (Q_sum3 Mptr1 Mint1 a j (1 + j) end1 i2) by auto with zarith.
    rewrite <- (Q_sum3 Mptr Mint b j (1 + j) end1 i2) by auto with zarith.

    rewrite <- (Q_sum3 Mptr1 Mint1 a (1 +j) i end1 i2) by auto with zarith.
    rewrite <- (Q_sum3 Mptr Mint b (1 + j) i end1 i2) by auto with zarith.

    rewrite (Z.add_shuffle3 (L_sum Mptr Mint b j (1 + j) i2)).
    rewrite Z.add_shuffle3.
    apply Zplus_eq_compat.
    apply Q_sum_4.
    all:auto with zarith.

    rewrite <- (Q_sum3 Mptr1 Mint1 a i (1 + i) end1 i2) by auto with zarith.
    rewrite <- (Q_sum3 Mptr Mint b i (1 + i) end1 i2) by auto with zarith.

    rewrite (Z.add_shuffle3 (L_sum Mptr Mint b j (1 + j) i2 )).
    apply Zplus_eq_compat.
    rewrite <- Q_sum2 by auto with zarith.
    rewrite <- Q_sum2 by auto with zarith.
    rewrite Q_sum1 by auto with zarith.
    rewrite Q_sum1 by auto with zarith.
    simpl.
    unfold P_same_array in H9.
    rewrite H9 by auto with zarith.
    reflexivity.

    apply Zplus_eq_compat.
    rewrite <- Q_sum2 by auto with zarith.
    rewrite <- Q_sum2 by auto with zarith.
    rewrite Q_sum1 by auto with zarith.
    rewrite Q_sum1 by auto with zarith.
    simpl.
    unfold P_same_array in H10.
    rewrite H10 by auto with zarith.
    reflexivity.

    apply Q_sum_4.
    all:auto with zarith.
* rewrite <- IHP_same_elements1.
  rewrite IHP_same_elements2.
  reflexivity.
  all:auto with zarith.
Qed.
