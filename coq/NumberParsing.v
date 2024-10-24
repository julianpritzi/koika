Require Import Koika.Frontend.
From Coq Require Decimal Hexadecimal.

Module NumberParsing.
  Inductive binary_literal sz :=
    | _binary_literal (b : bits sz).

  Module Import dec.
    Import Decimal.
    Fixpoint sz_of_dec_uint (d : Decimal.uint) :=
      match d with
      | Nil => 0
      | D0 d | D1 d | D2 d | D3 d | D4 d
      | D5 d | D6 d | D7 d | D8 d | D9 d
        => 1 + (sz_of_dec_uint d)
      end.
  End dec.

  Module Import hex.
    Import Hexadecimal.
    Fixpoint sz_of_hex_uint (d : Hexadecimal.uint) :=
      match d with
      | Nil => 0
      | D0 d | D1 d | D2 d | D3 d
      | D4 d | D5 d | D6 d | D7 d
      | D8 d | D9 d | Da d | Db d
      | Dc d | Dd d | De d | Df d
        => 1 + (sz_of_hex_uint d)
      end.
  End hex.

  Definition sz_of_num_uint (n : Number.uint) :=
    match n with
    | Number.UIntDecimal d => sz_of_dec_uint d
    | Number.UIntHexadecimal h => sz_of_hex_uint h
    end.


  Fixpoint bits_of_dec_uint (d: Decimal.uint) : option (Bits.bits (sz_of_dec_uint d)) :=
    match d as d' return (option (Bits.bits (sz_of_dec_uint d'))) with
    | Decimal.Nil => match sz_of_dec_uint d with _ => Some Bits.nil end
    | Decimal.D0 d => option_map (fun d' => Bits.snoc false d') (bits_of_dec_uint d)
    | Decimal.D1 d => option_map (fun d' => Bits.snoc true d') (bits_of_dec_uint d)
    | _ => None
    end.

  Definition binary_of_num_uint (d: Number.uint) : option (binary_literal (sz_of_num_uint d)) :=
    match d with
    | Number.UIntDecimal d => option_map (fun b => _binary_literal _ b) (bits_of_dec_uint d)
    | Number.UIntHexadecimal h => None
    end.

  Fixpoint pr' {sz} (b : bits sz) : Decimal.uint :=
    match sz as n return (bits n -> Decimal.uint) with
    | 0 => fun _ => Decimal.Nil
    | S _ => fun b' => if (Bits.hd b')
      then Decimal.D1 (pr' (Bits.tl b'))
      else Decimal.D0 (pr' (Bits.tl b'))
    end b.

  Definition pr {sz} (bl : binary_literal sz) : Number.uint :=
    match bl with
    | _binary_literal _ b => Number.UIntDecimal (pr' b)
    end.

  Declare Scope bitstrings_scope.
  Delimit Scope bitstrings_scope with bitstrings.
  (* Arguments binary_literal {sz} : assert. *)
  (* Number Notation binary_literal binary_of_num_uint pr : bitstrings_scope. *)
  (* Check 0110101%bitstrings. *)
  (* Compute 0110101%bitstrings. *)

  Definition binary_literal_to_bits {sz} (bl : binary_literal sz) : bits sz :=
    match bl with
    | _binary_literal _ b => b
    end.
  
  Import (notations) Decimal.
  Notation "'0b' num" :=
    (must (option_map binary_literal_to_bits (binary_of_num_uint num%uint)))
    (at level 2, num constr at level 0, no associativity).


  (* Check (0b11).
  Compute 0b101101.
  Compute 0x1233. *)
End NumberParsing.
