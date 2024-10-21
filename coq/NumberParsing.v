Require Import Koika.Frontend.

(* Inductive parsed_bit_list :=
| Nil_bit_list
| Cons_bit_list : forall (b: bool) (bs: parsed_bit_list), parsed_bit_list. *)

Print Decimal.uint.

Import Decimal.

Fixpoint sz_of_dec_uint (d : Decimal.uint) :=
  match d with
  | Nil => 0
  | D0 d | D1 d | D2 d | D3 d | D4 d
  | D5 d | D6 d | D7 d | D8 d | D9 d
    => 1 + (sz_of_dec_uint d)
  end.

Definition sz_of_num_uint (n : Number.uint) :=
  match n with
  | Number.UIntDecimal d => sz_of_dec_uint d
  | Number.UIntHexadecimal h => 0
  end.

(* Fixpoint bits_of_dec_uint (d: Decimal.uint) : option (Bits.bits (sz_of_dec_uint d)).
  destruct d.
  unfold sz_of_dec_uint. exact (Some Bits.nil).

  unfold sz_of_dec_uint. exact (Some (@Bits.cons (sz_of_dec_uint d) false (bits_of_dec_uint d))).
  all: exact None.
Defined. *)

(* Print bits_of_dec_uint. *)
  

Fixpoint bits_of_dec_uint (d: Decimal.uint) : option (Bits.bits (sz_of_dec_uint d)) :=
    match d as d' return (option (Bits.bits (sz_of_dec_uint d'))) with
    | Decimal.Nil => match sz_of_dec_uint d with _ => Some Bits.nil end
    | Decimal.D0 d => option_map (fun d' => Bits.snoc false d') (bits_of_dec_uint d)
    | Decimal.D1 d => option_map (fun d' => Bits.snoc true d') (bits_of_dec_uint d)
    | _ => None
    end.

Definition bits_of_num_uint (d: Number.uint) : option (Bits.bits (sz_of_num_uint d)) :=
  match d with
  | Number.UIntDecimal d =>
    bits_of_dec_uint d
  | Number.UIntHexadecimal h => None
  end.

Compute (bits_of_num_uint 01101%uint).
(* 
Fixpoint decode_bitstring_from_bits (sz: nat) (bs: parsed_bit_list) : option (bits sz) :=
  match sz with
  | 0 =>
    match bs with
    | Nil_bit_list => Some Ob
    | _ => None
    end
  | S sz =>
    let/opt2 hd, bs :=
       match bs with
       | Nil_bit_list => Some (false, bs)
       | Cons_bit_list hd bs => Some (hd, bs)
       end in
    let/opt tl :=
       decode_bitstring_from_bits sz bs in
    Some tl~hd
  end. *)

Inductive NumberParsingError :=
  NumberParsingError_OutOfBounds.

Definition must_bits {sz} (o: option (bits sz)) : if o then bits sz else NumberParsingError :=
  match o with
  | Some bs => bs
  | None => NumberParsingError_OutOfBounds
  end.

Fixpoint pr' {sz} (b : bits sz) : Decimal.uint :=
  match sz as n return (bits n -> Decimal.uint) with
  | 0 => fun _ => Decimal.Nil
  | S _ => fun b' => if (Bits.hd b')
    then Decimal.D1 (pr' (Bits.tl b'))
    else Decimal.D0 (pr' (Bits.tl b'))
  end b.

Definition pr {sz} (bl : bits sz) : Number.uint :=
  Number.UIntDecimal (pr' bl).



Declare Scope bitstrings_scope.
Delimit Scope bitstrings_scope with bitstrings.
(* Number Notation bits decode_bits_from_parsed_uint pr : bitstrings_scope. *)
(* Notation "'0b' num ':b' sz" :=
  (tc_compute (must_bits (decode_bitstring_from_bits sz num%bitstrings) : bits sz))
    (at level 2, no associativity).

Check 0110101%bitstrings.

Check (0b11:b32).                 FIXME remove type annotation *)
