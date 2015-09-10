From Ssreflect
     Require Import ssreflect ssrbool eqtype ssrnat seq tuple.
From Bits
     Require Import spec.spec spec.operations spec.operations.properties.

(** * An axiomatization of OCaml native integers *)

(**

This axiomatization is based on "native-coq"
(https://github.com/maximedenes/native-coq)

 *)

(** ** Base type and operations *)

Definition wordsize := 63.

Axiom Int63: Type.
Extract Inlined Constant Int63 => "int".

(** We say that an [n : Int63] is the representation of a bitvector
[bs : BITS 63] if they satisfy the axiom [repr_native]. Morally, it
means that both represent the same number (ie. the same 63
booleans). *)

Axiom native_repr: Int63 -> BITS wordsize -> Prop.

(** This extends to natural numbers, going through a [BITS wordsize]
word. *)

Definition natural_repr: Int63 -> nat -> Prop :=
  fun i n =>
    exists bs, native_repr i bs /\ # n = bs.


(** We axiomatize the following operations from OCaml: *)

Axiom leq: Int63 -> Int63 -> bool.
Extract Inlined Constant leq => "(=)".

Axiom leq_repr:
  forall i i' bs bs',
    native_repr i bs -> native_repr i' bs' ->
    (leq i i') = (bs == bs').


Axiom lnot: Int63 -> Int63.
Extract Inlined Constant lnot => "lnot".

Axiom lnot_repr:
  forall i bs,
    native_repr i bs ->
    native_repr (lnot i) (invB bs).


Axiom land: Int63 -> Int63 -> Int63.
Extract Inlined Constant land => "(land)".

Axiom land_repr:
  forall i i' bs bs',
    native_repr i bs -> native_repr i' bs' ->
    native_repr (land i i') (andB bs bs').


Axiom lor: Int63 -> Int63 -> Int63.
Extract Inlined Constant lor => "(lor)".

Axiom lor_repr:
  forall i i' bs bs',
    native_repr i bs -> native_repr i' bs' ->
    native_repr (lor i i') (orB bs bs').


Axiom lxor: Int63 -> Int63 -> Int63.
Extract Inlined Constant lxor => "(lxor)".

Axiom lxor_repr:
  forall i i' bs bs',
    native_repr i bs -> native_repr i' bs' ->
    native_repr (lxor i i') (xorB bs bs').


Axiom lsr: Int63 -> Int63 -> Int63.
Extract Inlined Constant lsr => "(lsr)".

Axiom lsr_repr:
  forall i j bs k,
    native_repr i bs -> natural_repr j k ->
    native_repr (lsr i j) (shrBn bs k).


Axiom lsl: Int63 -> Int63 -> Int63.
Extract Inlined Constant lsl => "(lsl)".

Axiom lsl_repr:
  forall i j bs k,
    native_repr i bs -> natural_repr j k ->
    native_repr (lsl i j) (shlBn bs k).


Axiom lneg: Int63 -> Int63.
Extract Inlined Constant lneg => "-".

Axiom lneg_repr:
  forall i bs,
    native_repr i bs ->
    native_repr (lneg i) (negB bs).


Axiom ldec: Int63 -> Int63.
Extract Inlined Constant ldec => "(fun x -> x - 1)".

Axiom ldec_repr:
  forall i bs,
    native_repr i bs ->
    native_repr (ldec i) (decB bs).


Axiom ladd: Int63 -> Int63 -> Int63.
Extract Inlined Constant ladd => "(+)".

Axiom ladd_repr:
  forall i i' bs bs',
    native_repr i bs -> native_repr i' bs' ->
    native_repr (ladd i i') (addB bs bs').


Axiom zero : Int63.
Extract Inlined Constant zero => "0".

Axiom zero_repr: native_repr zero #0.


Axiom one : Int63.
Extract Inlined Constant one => "1".

Axiom one_repr: native_repr one #1.


Axiom succ : Int63 -> Int63.
Extract Inlined Constant succ => "(fun x -> x + 1)".

Axiom succ_repr:
  forall i bs,
    native_repr i bs ->
    native_repr (succ i) (incB bs).


Fixpoint toInt (bs: seq bool)(k: Int63): Int63 :=
  match bs with
    | [::] => zero
    | [:: false & bs] => toInt bs (succ k)
    | [:: true & bs ] => lor (lsl one k) (toInt bs (succ k))
  end.

(** Careful, this is painfully slow... *)
Definition toInt63 (bs: BITS wordsize): Int63 := toInt bs zero.

Axiom toInt63_repr:
  forall bs,
    native_repr (toInt63 bs) bs.


Fixpoint fromInt (n: Int63)(k: nat): seq bool :=
  match k with 
    | 0 => [::]
    | k.+1 =>
      [:: leq (land (lsr n (toInt63 #(wordsize - k.+1))) one) one &
          fromInt n k]
  end.

Lemma fromInt63P {k} (n: Int63): size (fromInt n k) == k.
Proof.
  elim: k=> // [k IH].
Qed.

Canonical fromInt63 (n: Int63): BITS 63
  := Tuple (fromInt63P n).

Axiom fromInt63_repr:
  forall i bs,
    native_repr i (fromInt63 i).