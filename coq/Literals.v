From Koika Require Import
  SyntaxMacros
  Types
  Vect
  IdentParsing
  Primitives.
From Coq Require Specif.
Import (notations) Specif.SigTNotations.

(* Bits.of_N with an inferred length or a default if inference fails *)
Ltac bits_of_N default val :=
  exact (Bits.of_N default val) + exact (Bits.of_N _ val).
Local Definition len := String.length.

(* Koika_var *)
Declare Custom Entry koika_literal_var.
Notation "a" := (ident_to_string a) (in custom koika_literal_var at level 0, a ident, only parsing).
Notation "a" := (a) (in custom koika_literal_var at level 0, a ident, format "'[' a ']'", only printing).

Declare Custom Entry koika_literal.
From Coq Require Import (notations) String.

(* ========================================================================= *)
(*                            bit vector literals                            *)
(* ========================================================================= *)

Notation "num ':b' sz" :=      (Bits.of_N (sz <: nat)            (bin_string_to_N num%string)) (in custom koika_literal at level 0, num constr at level 0, sz constr at level 0, only parsing).
Notation "num ':b'"    := ltac:(bits_of_N ((len num) * 1)        (bin_string_to_N num%string)) (in custom koika_literal at level 0, num constr at level 0,                       only parsing).
Notation "'0b' num sz" :=      (Bits.of_N (sz <: nat)            (bin_string_to_N num%string)) (in custom koika_literal at level 0, num constr at level 0, sz constr at level 0, format "'0b' num sz").
Notation "'0b' num"    := ltac:(bits_of_N ((len num) * 1)        (bin_string_to_N num%string)) (in custom koika_literal at level 0, num constr at level 0,                       only parsing).
Notation "'0b' num"    :=      (Bits.of_N _                      (bin_string_to_N num%string)) (in custom koika_literal at level 0, num constr at level 0, only printing,        format "'0b' num").

Notation "num ':o' sz" :=      (Bits.of_N (sz <: nat)            (oct_string_to_N num%string)) (in custom koika_literal at level 0, num constr at level 0, sz constr at level 0, only parsing).
Notation "num ':o'"    := ltac:(bits_of_N ((len num) * 3)        (oct_string_to_N num%string)) (in custom koika_literal at level 0, num constr at level 0,                       only parsing).
Notation "'0o' num sz" :=      (Bits.of_N (sz <: nat)            (oct_string_to_N num%string)) (in custom koika_literal at level 0, num constr at level 0, sz constr at level 0, format "'0o' num sz").
Notation "'0o' num"    := ltac:(bits_of_N ((len num) * 3)        (oct_string_to_N num%string)) (in custom koika_literal at level 0, num constr at level 0,                       only parsing).
Notation "'0o' num"    :=      (Bits.of_N _                      (oct_string_to_N num%string)) (in custom koika_literal at level 0, num constr at level 0, only printing,        format "'0o' num").

Notation "num ':d' sz" :=      (Bits.of_N (sz <: nat)            (dec_string_to_N num%string)) (in custom koika_literal at level 0, num constr at level 0, sz constr at level 0, only parsing).
Notation "num ':d'"    := ltac:(bits_of_N (1 + (N.to_nat (N.log2 (dec_string_to_N num%string))))
                                                                 (dec_string_to_N num%string)) (in custom koika_literal at level 0, num constr at level 0,                       only parsing).
Notation "'0d' num sz" :=      (Bits.of_N (sz <: nat)            (dec_string_to_N num%string)) (in custom koika_literal at level 0, num constr at level 0, sz constr at level 0, format "'0d' num sz").
Notation "'0d' num"    := ltac:(bits_of_N (1 + (N.to_nat (N.log2 (dec_string_to_N num%string))))
                                                                 (dec_string_to_N num%string)) (in custom koika_literal at level 0, num constr at level 0,                       only parsing).
Notation "'0d' num"    :=      (Bits.of_N _                      (dec_string_to_N num%string)) (in custom koika_literal at level 0, num constr at level 0, only printing,        format "'0d' num").

Notation "num ':h' sz" :=      (Bits.of_N (sz <: nat)            (hex_string_to_N num%string)) (in custom koika_literal at level 0, num constr at level 0, sz constr at level 0, only parsing).
Notation "num ':h'"    := ltac:(bits_of_N ((len num) * 4)        (hex_string_to_N num%string)) (in custom koika_literal at level 0, num constr at level 0,                       only parsing).
Notation "'0x' num sz" :=      (Bits.of_N (sz <: nat)            (hex_string_to_N num%string)) (in custom koika_literal at level 0, num constr at level 0, sz constr at level 0, format "'0x' num sz").
Notation "'0x' num"    := ltac:(bits_of_N ((len num) * 4)        (hex_string_to_N num%string)) (in custom koika_literal at level 0, num constr at level 0,                       only parsing).
Notation "'0x' num"    :=      (Bits.of_N _                      (hex_string_to_N num%string)) (in custom koika_literal at level 0, num constr at level 0, only printing,        format "'0x' num").

(* literal inside constr (normal Coq) - directly usable as [bits n] *)
Notation "'|' literal '|'" := (literal) (at level 10, literal custom koika_literal).

(* ========================================================================= *)
(*                         koika Notations for constr                        *)
(* ========================================================================= *)

(* Transforming a list of actions into a sequence of
 * substitute operations to initialize a struct *)
Fixpoint struct_init
  (sig: struct_sig) (fields: list {idx : struct_index sig & field_type sig idx})
  : struct_t sig :=  match fields with
  | cons (idx; val) fields' =>
    BitFuns.subst_field sig.(struct_fields) (struct_init sig fields') (idx) (val)
  | nil => value_of_bits Bits.zero
  end.

Class FieldSubstConstr {T} {sig : struct_sig} (field : string) (val : T) :=
  field_subst_constr : {idx : struct_index sig & field_type sig idx}.
Hint Mode FieldSubstConstr + + + + : typeclass_instances.
Arguments field_subst_constr {T} {sig} field val {FieldSubstConstr}.
Hint Extern 1 (@FieldSubstConstr _ ?sig ?field ?val) => exact (must (List_assoc field sig.(struct_fields)) ; val) : typeclass_instances.

(* create struct literals in constr (normal Coq) *)
(* using Ltac to defer the typechecking until the term is fully constructed *)
Declare Custom Entry koika_struct_literal.
Declare Custom Entry koika_struct_literal_field.
Notation "f ':=' expr" := (field_subst_constr f expr)
  (in custom koika_struct_literal_field at level 0, f custom koika_literal_var, expr constr).
Notation "a ';' b" := (cons a b)   (in custom koika_struct_literal at level 0, a custom koika_struct_literal_field, right associativity).
Notation "a ';'"   := (cons a nil) (in custom koika_struct_literal at level 0, a custom koika_struct_literal_field). (* trailing comma *)
Notation "a"       := (cons a nil) (in custom koika_struct_literal at level 0, a custom koika_struct_literal_field).

(*
The notations which start directly with a variable need to be at level 1
else they interfere with the notations in koika.
E.g.
  `struct sig ::{ ... }` in koika parses sig as constr 0, but
  if the syntax sig ::{ } is in constr 0, then the braces will
  also unintentionally be parsed as part of sig
*)
Notation "'struct' sig '::{' '}'" :=
  (struct_init sig []) (sig constr at level 0, format "struct  sig ::{  }").
Notation "'struct' sig '::{' fields '}'" :=
  (struct_init sig fields) (sig constr at level 0, fields custom koika_struct_literal, format "struct  sig ::{  fields  }").

Notation "sig '::{' '}'" :=
  (struct_init sig []) (at level 1, format "sig ::{  }").
Notation "sig '::{' fields '}'" :=
  (struct_init sig fields) (at level 1, fields custom koika_struct_literal, format "sig ::{  fields  }").

(* creating enums literal in constr (normal Coq) *)
Notation "'enum' sig '::<' f '>'" :=
  ((vect_nth sig.(enum_bitpatterns)) (must (vect_index f sig.(enum_members))))
    (sig constr at level 0, f custom koika_literal_var, format "enum  sig ::< f >").
Notation "sig '::<' f '>'" :=
  ((vect_nth sig.(enum_bitpatterns)) (must (vect_index f sig.(enum_members))))
    (at level 1, sig constr, f custom koika_literal_var, format "sig ::< f >").

Module Type Tests.

  Definition num_test_constr_1 := |"0110":b|     : bits _.
  Definition num_test_constr_2 := |0b"0110"|     : bits _.
  Definition num_test_constr_3 := |"c0ffee":h|   : bits _.
  Definition num_test_constr_4 := |0x"deadbeef"| : bits _.

  Definition numbers_e := {|
    enum_name        := "some_enum_name";
    enum_members     :=                          [ "ONE"; "TWO"; "THREE"; "IDK" ];
    enum_bitpatterns := vect_map (Bits.of_nat 3) [ 1    ; 2    ; 3      ; 7     ]
  |}%vect.

  Definition enum_test_1 := enum numbers_e::< ONE >.
  Definition enum_test_2 := enum numbers_e::< TWO >.
  Definition enum_test_3 :  enum numbers_e::< ONE >   = |"001":b| := eq_refl.
  Definition enum_test_4 :  enum numbers_e::< TWO >   = |"010":b| := eq_refl.
  Definition enum_test_5 :  enum numbers_e::< THREE > = |"011":b| := eq_refl.
  Definition enum_test_6 :  enum numbers_e::< IDK >   = |"111":b| := eq_refl.

  Definition numbers_s := {|
    struct_name:= "numbers_s";
    struct_fields :=
    [ ("one"  , bits_t 3);
      ("two"  , bits_t 3);
      ("three", bits_t 3);
      ("four" , bits_t 3);
      ("five" , enum_t numbers_e) ]
  |}.

  Definition struct_test_1 := struct numbers_s::{ }.
  Definition struct_test_2 :  struct numbers_s::{ } = value_of_bits Bits.zero := eq_refl.
  Definition struct_test_3 := struct numbers_s::{ one := |"010":b| }.
  Definition struct_test_7 := struct numbers_s::{ one := Bits.of_N 3 3; two := Bits.of_N 3 2; }. (* trailing comma *)
  Definition struct_test_4 :  struct numbers_s::{ one := |"010":b| ; two := |"111":b| } = (Ob~0~1~0, (Ob~1~1~1, (Ob~0~0~0, (Ob~0~0~0, (Ob~0~0~0, tt))))) := eq_refl.
  Definition struct_test_5 :  struct numbers_s::{ five := enum numbers_e::< IDK > }     = (Ob~0~0~0, (Ob~0~0~0, (Ob~0~0~0, (Ob~0~0~0, (Ob~1~1~1, tt))))) := eq_refl.
  Fail Definition struct_test_6 := struct numbers_s::{ five := enum numbers_e::< WRONG > }.
  Fail Definition struct_test_8 := struct numbers_s::{ wrong := Bits.of_N 3 3 }.
End Tests.
