(*! Frontend | Parser for the Kôika EDSL !*)
Require Import
        Koika.Common
        Koika.Syntax
        Koika.IdentParsing.

Export Koika.Types.SigNotations.
Export Koika.Primitives.PrimUntyped.
Export Coq.Strings.String.
Export Coq.Lists.List.ListNotations.

Declare Custom Entry koika.

(* This is the entry point to transition from normal
  Coq (constr) to koika *)
Notation "'{{' e '}}'" := (e) (e custom koika at level 200, format "'{{' '[v' '/' e '/' ']' '}}'").

(* Koika_var *)
Declare Custom Entry koika_var.
Notation "a" := (ident_to_string a) (in custom koika_var at level 0, a constr at level 0, only parsing).
Notation "a" := (a) (in custom koika_var at level 0, a constr at level 0, format "'[' a ']'", only printing).

(* koika_binder *)
Declare Custom Entry koika_binder.
Notation "'(' x ':' y ')'" := (x%string, y : type) (in custom koika_binder at level 0, x custom koika_var, y constr).
Notation "a .. b" := (cons a ..  (cons b nil) ..)  (in custom koika_binder at level 1, a custom koika_binder at next level, b custom koika_binder at next level).

Notation "'fun' nm args ':' ret '=>' body" :=
  (Build_UInternalFunction nm%string args ret body)
    (in custom koika at level 200, nm custom koika_var, args custom koika_binder, ret constr at level 0, right associativity, format "'[v' 'fun'  nm  args  ':'  ret  '=>' '/' body ']'").
Notation "'fun' nm '()' ':' ret '=>' body" :=
  (Build_UInternalFunction nm%string nil ret body)
    (in custom koika at level 200, nm custom koika_var, ret constr at level 0, right associativity, format "'[v' 'fun'  nm  '()'   ':'  ret  '=>' '/' body ']'").

Notation "'assert' a 'in' c"          := (UIf a c (USugar (UConstBits Ob))) (in custom koika at level 200, right associativity, format "'[v' 'assert'  a '/' 'in'  c ']'").
Notation "'assert' a 'else' b 'in' c" := (UIf a c b                       ) (in custom koika at level 200, right associativity, format "'[v' 'assert'  a '/' 'else'  b '/' 'in'  c ']'").
Notation "'when' a 'do' t "           := (UIf a t (USugar (UConstBits Ob))) (in custom koika at level 200, right associativity, format "'[v' 'when'  a '/' 'do'  t '/' ']'").

Notation "'let' a ':=' b 'in' c" := (UBind a b c) (in custom koika at level 200, a custom koika_var, right associativity, format "'[v' 'let'  a  ':='  b  'in' '/' c ']'").

Notation "a ';' b" := (USeq a                        b) (in custom koika at level 90, b at level 200, format "'[v' a ';' '/' b ']'" ).
Notation "a ';'"   := (USeq a (USugar (UConstBits Ob))) (in custom koika at level 90). (* trailing comma *)


Notation "'set' a ':=' b" := (UAssign a b) (in custom koika at level 89, a custom koika_var, format "set  a  :=  b").

Notation "'if' a 'then' t 'else' f" := (UIf a t f) (in custom koika at level 89, right associativity, format "'[v' 'if'  a '/' 'then'  t '/' 'else'  f ']'").
Notation "'guard' '(' a ')' " := (UIf (UUnop (UBits1 UNot) a) (UFail (bits_t 0)) (USugar (UConstBits Ob))) (in custom koika at level 89, right associativity, format "guard ( a )").

(* Inspired by cpp precedence  *)
(* https://en.cppreference.com/w/cpp/language/operator_precedence *)
(* TODO id really prefer to use || and && for logical operations and & | for bitwise *)
(* Bit operations *)
Notation "a  '||'  b"  := (UBinop (UBits2     UOr)              a b) (in custom koika at level 85).
Notation "a  '^'  b"   := (UBinop (UBits2    UXor)              a b) (in custom koika at level 84).
Notation "a  '&&'  b"  := (UBinop (UBits2    UAnd)              a b) (in custom koika at level 83).

(* Comparisons *)
Notation "a  '!='  b"  := (UBinop (UEq true)                    a b) (in custom koika at level 80).
Notation "a  '=='  b"  := (UBinop (UEq false)                   a b) (in custom koika at level 80).

Notation "a  '<'  b"   := (UBinop (UBits2 (UCompare false cLt)) a b) (in custom koika at level 79).
Notation "a  '<s'  b"  := (UBinop (UBits2 (UCompare true  cLt)) a b) (in custom koika at level 79).
Notation "a  '<='  b"  := (UBinop (UBits2 (UCompare false cLe)) a b) (in custom koika at level 79).
Notation "a  '<s='  b" := (UBinop (UBits2 (UCompare true  cLe)) a b) (in custom koika at level 79).
Notation "a  '>'  b"   := (UBinop (UBits2 (UCompare false cGt)) a b) (in custom koika at level 79).
Notation "a  '>s'  b"  := (UBinop (UBits2 (UCompare true  cGt)) a b) (in custom koika at level 79).
Notation "a  '>='  b"  := (UBinop (UBits2 (UCompare false cGe)) a b) (in custom koika at level 79).
Notation "a  '>s='  b" := (UBinop (UBits2 (UCompare true  cGe)) a b) (in custom koika at level 79).

(* Bit concatenation / shifts *)
Notation "a  '++'  b"  := (UBinop (UBits2 UConcat)              a b) (in custom koika at level 75).
Notation "a  '>>'  b"  := (UBinop (UBits2 ULsr)                 a b) (in custom koika at level 74).
Notation "a  '>>>'  b" := (UBinop (UBits2 UAsr)                 a b) (in custom koika at level 74).
Notation "a  '<<'  b"  := (UBinop (UBits2 ULsl)                 a b) (in custom koika at level 74).

(* Arithmetic *)
Notation "a  '+'  b"   := (UBinop (UBits2   UPlus)              a b) (in custom koika at level 70).
Notation "a  '-'  b"   := (UBinop (UBits2  UMinus)              a b) (in custom koika at level 70).
Notation "a  '*'  b"   := (UBinop (UBits2    UMul)              a b) (in custom koika at level 69).

(* Unary operators *)
Notation "'!' a"       := (UUnop (UBits1 UNot) a)                    (in custom koika at level 65, format "'!' a").

(* Accessors *)
Notation "a '[' b ']'"        := (UBinop (UBits2 USel)              a b) (in custom koika at level 60, format "'[' a [ b ] ']'").
Notation "a '[' b ':+' c ']'" := (UBinop (UBits2 (UIndexedSlice c)) a b) (in custom koika at level 60, c constr at level 0, format "'[' a [ b ':+' c ] ']'").

(* get field of struct *)
Notation "a '.[' f ']'" := (UUnop  (UStruct1 (UGetField f)) a) (in custom koika at level 60, f custom koika_var).


Notation "'`' a '`'" := (a) (in custom koika, a constr).
Notation "'(' a ')'" := (a) (in custom koika, a custom koika, format "'[v' '(' a ')' ']'").

Notation "'#' s" := (USugar (UConstBits s)) (in custom koika at level 0, s constr at level 0, only parsing).

(* ========================================================================= *)
(*                   Notations beginning with an identifier                  *)
(* ========================================================================= *)
(*
Note:
  All these notations need to be on the same level (here 0)
  else the parser would match on the highest level first and
  never even consider notations on a lower level.

  Likewise, all these notations need to start with a variable
  on the same level and in the same grammar (here a constr on level 0).
  Only so the parser can parse this variable first and then decide
  (depending on the following tokens) which notation matches.

Note:
  Some of the literal notations also start with an identifier.
  Thus, the same restrictions apply.
*)
Notation "a" := (UVar (ident_to_string a)) (in custom koika at level 0, a constr at level 0, only parsing).
Notation "a" := (UVar a) (in custom koika at level 0, a constr at level 0, only printing).

(* Alternative shorter set syntax
Note: expr is level 89 to stay below ';'
*)
Export (hints) IdentParsing.TC.
Notation "a ':=' b" := (let aa := (TC.ident_to_string a) in UAssign aa b) (in custom koika at level 0, a constr at level 0, b custom koika at level 89, only parsing).
Notation "a ':=' b" := (UAssign a b)                                      (in custom koika at level 0, a constr at level 0, b custom koika at level 89, only printing).


(* Koika_args *)
Declare Custom Entry koika_args.
Notation "'(' x ',' .. ',' y ')'" := (cons x .. (cons y nil) ..)(in custom koika_args, x custom koika, y custom koika).
Notation "'(' ')'" := nil (in custom koika_args).
Notation "'()'"    := nil (in custom koika_args).

Notation "fn args"                    := (USugar (UCallModule id       _ fn args))
    (in custom koika at level 0, fn constr at level 0 , args custom koika_args, only parsing).

Notation "instance  '.(' fn ')' args" := (USugar (UCallModule instance _ fn args))
    (in custom koika at level 0, instance constr at level 0, fn constr, args custom koika_args).

Notation "'{' fn '}' args"            := (USugar (UCallModule id       _ fn args))
    (in custom koika at level 0, fn constr , args custom koika_args, only parsing).


(* ========================================================================= *)
(*                                  Literals                                 *)
(* ========================================================================= *)

(* Koika_consts *)
Declare Custom Entry koika_consts.
Notation "'1'" := (Ob~1) (in custom koika_consts at level 0).
Notation "'0'" := (Ob~0) (in custom koika_consts at level 0).
Notation "bs '~' '0'" := (Bits.cons false bs) (in custom koika_consts at level 1, left associativity, format "bs '~' '0'").
Notation "bs '~' '1'" := (Bits.cons true bs)  (in custom koika_consts at level 1, left associativity, format "bs '~' '1'").

Notation "'Ob' '~' number" := (USugar (UConstBits number))
  (in custom koika at level 0, number custom koika_consts, format "'Ob' '~' number").
Notation "'Ob'"            := (USugar (UConstBits Bits.nil))
  (in custom koika at level 0).



(* koika bit vector literals *)
From Coq Require BinaryString OctalString HexString HexadecimalString DecimalString.

(* Unset Printing Notations.
From Coq Require Ascii.

Compute (list_ascii_of_string "_").
Compute (String "_" EmptyString). *)

Require Import Ascii.
Local Fixpoint filters' (s : string) (a : ascii) : string :=
  match s with
  | EmptyString => EmptyString
  | String c s' => if ascii_dec c a
    then filters' s' a
    else String c (filters' s' a)
  end.
Local Fixpoint filters (s : string) (l : list ascii) : string :=
  match l with
  | a :: l' => filters (filters' s a) l'
  | [] => s
  end.

(* Coq's implementation just silently returns 0 on an invalid string -
  for better error recognition these methods are redefined here returning option *)
Local Fixpoint num_string_to_option_N' (s : string) (base : N) (convert : Ascii.ascii -> option N) (remainder : option N) : option N :=
  match s with
  | EmptyString => remainder
  | String c s' => num_string_to_option_N' s' base convert
    (match remainder, convert c with
    | Some rem, Some c_v => Some (N.add (N.mul base rem) c_v)
    | _, _ => None
    end)
  end.
Local Definition num_string_to_option_N (s : string) (base : N) (convert : Ascii.ascii -> option N) : option N :=
  match s with
  | EmptyString => None
  | String _ _ => num_string_to_option_N' s base convert (Some 0%N)
  end.

Local Definition bin_string_to_N s := (must (num_string_to_option_N s 2 BinaryString.ascii_to_digit)).
Local Definition oct_string_to_N s := (must (num_string_to_option_N s 8 OctalString.ascii_to_digit)).
Local Definition dec_string_to_N s := (must (option_map N.of_uint (DecimalString.NilZero.uint_of_string s))).
Local Definition hex_string_to_N s := (must (num_string_to_option_N s 16 HexString.ascii_to_digit)).

Local Definition len := String.length.
Local Definition filt s := filters s ["_"; "'"]%char.

Notation "num ':b' sz" := (let s := filt num in (USugar (UConstBits (Bits.of_N (sz <: nat)            (bin_string_to_N s))))) (in custom koika at level 0, num constr at level 0, sz constr at level 0, only parsing).
Notation "num ':b'"    := (let s := filt num in (USugar (UConstBits (Bits.of_N ((len s) * 1)          (bin_string_to_N s))))) (in custom koika at level 0, num constr at level 0,                       only parsing).
Notation "'0b' num sz" := (let s := filt num in (USugar (UConstBits (Bits.of_N (sz <: nat)            (bin_string_to_N s))))) (in custom koika at level 0, num constr at level 0, sz constr at level 0, format "'0b' num sz").
Notation "'0b' num"    := (let s := filt num in (USugar (UConstBits (Bits.of_N ((len s) * 1)          (bin_string_to_N s))))) (in custom koika at level 0, num constr at level 0,                       only parsing).
Notation "'0b' num"    := (let s := filt num in (USugar (UConstBits (Bits.of_N _                      (bin_string_to_N s))))) (in custom koika at level 0, num constr at level 0, only printing,        format "'0b' num").

Notation "num ':o' sz" := (let s := filt num in (USugar (UConstBits (Bits.of_N (sz <: nat)            (oct_string_to_N s))))) (in custom koika at level 0, num constr at level 0, sz constr at level 0, only parsing).
Notation "num ':o'"    := (let s := filt num in (USugar (UConstBits (Bits.of_N ((len s) * 3)          (oct_string_to_N s))))) (in custom koika at level 0, num constr at level 0,                       only parsing).
Notation "'0o' num sz" := (let s := filt num in (USugar (UConstBits (Bits.of_N (sz <: nat)            (oct_string_to_N s))))) (in custom koika at level 0, num constr at level 0, sz constr at level 0, format "'0o' num sz").
Notation "'0o' num"    := (let s := filt num in (USugar (UConstBits (Bits.of_N ((len s) * 3)          (oct_string_to_N s))))) (in custom koika at level 0, num constr at level 0,                       only parsing).
Notation "'0o' num"    := (let s := filt num in (USugar (UConstBits (Bits.of_N _                      (oct_string_to_N s))))) (in custom koika at level 0, num constr at level 0, only printing,        format "'0o' num").

Notation "num ':d' sz" := (let s := filt num in (USugar (UConstBits (Bits.of_N (sz <: nat)            (dec_string_to_N s))))) (in custom koika at level 0, num constr at level 0, sz constr at level 0, only parsing).
Notation "num ':d'"    := (let s := filt num in (USugar (UConstBits (Bits.of_N (1 + (N.to_nat (N.log2 (dec_string_to_N s))))
                                                            (dec_string_to_N s))))) (in custom koika at level 0, num constr at level 0,                       only parsing).
Notation "'0d' num sz" := (let s := filt num in (USugar (UConstBits (Bits.of_N (sz <: nat)            (dec_string_to_N s))))) (in custom koika at level 0, num constr at level 0, sz constr at level 0, format "'0d' num sz").
Notation "'0d' num"    := (let s := filt num in (USugar (UConstBits (Bits.of_N (1 + (N.to_nat (N.log2 (dec_string_to_N s))))
                                                            (dec_string_to_N s))))) (in custom koika at level 0, num constr at level 0,                       only parsing).
Notation "'0d' num"    := (let s := filt num in (USugar (UConstBits (Bits.of_N _                      (dec_string_to_N s))))) (in custom koika at level 0, num constr at level 0, only printing,        format "'0d' num").

Notation "num ':h' sz" := (let s := filt num in (USugar (UConstBits (Bits.of_N (sz <: nat)            (hex_string_to_N s))))) (in custom koika at level 0, num constr at level 0, sz constr at level 0, only parsing).
Notation "num ':h'"    := (let s := filt num in (USugar (UConstBits (Bits.of_N ((len s) * 4)          (hex_string_to_N s))))) (in custom koika at level 0, num constr at level 0,                       only parsing).
Notation "'0x' num sz" := (let s := filt num in (USugar (UConstBits (Bits.of_N (sz <: nat)            (hex_string_to_N s))))) (in custom koika at level 0, num constr at level 0, sz constr at level 0, format "'0x' num sz").
Notation "'0x' num"    := (let s := filt num in (USugar (UConstBits (Bits.of_N ((len s) * 4)          (hex_string_to_N s))))) (in custom koika at level 0, num constr at level 0,                       only parsing).
Notation "'0x' num"    := (let s := filt num in (USugar (UConstBits (Bits.of_N _                      (hex_string_to_N s))))) (in custom koika at level 0, num constr at level 0, only printing,        format "'0x' num").

(* legacy number format *)
(* TODO remove to prevent abiguity with trailing semicolons followed by match branches *)
Notation "'|' a '`d' b '|'" :=
  (USugar (UConstBits (Bits.of_N (a<:nat) b%N)))
    (in custom koika, a constr at level 0 , b constr at level 0).

(* ========================================================================= *)
(*                                Constructors                               *)
(* ========================================================================= *)

Declare Custom Entry koika_struct.
Declare Custom Entry koika_struct_field.
(* expr at level at level 89 to stay below koika's sequence (a ; b) *)
Notation "f ':=' expr" := (f, expr) (in custom koika_struct_field at level 0, f custom koika_var, expr custom koika at level 89).
Notation "a ';' b" := (cons a   b) (in custom koika_struct at level 0, a custom koika_struct_field, right associativity).
Notation "a ';'"   := (cons a nil) (in custom koika_struct at level 0, a custom koika_struct_field). (* trailing comma *)
Notation "a"       := (cons a nil) (in custom koika_struct at level 0, a custom koika_struct_field).

Notation "'struct' sig '{' '}'"        := (USugar (UStructInit sig []))
  (in custom koika, sig constr at level 0).
Notation "'struct' sig '{' fields '}'" := (USugar (UStructInit sig fields))
  (in custom koika, sig constr at level 0, fields custom koika_struct).
Notation "'enum' sig '{' mem '}'"      := (USugar (UConstEnum sig mem))
  (in custom koika, sig constr at level 0, mem custom koika_var).


Notation "sig '::{' '}'"        := (USugar (UStructInit sig []))
  (in custom koika at level 0, sig constr at level 0).
Notation "sig '::{' fields '}'" := (USugar (UStructInit sig fields))
  (in custom koika at level 0, sig constr at level 0, fields custom koika_struct).
Notation "sig '::<' mem '>'"    := (USugar (UConstEnum sig mem))
  (in custom koika at level 0, sig constr at level 0, mem custom koika_var).


(* ========================================================================= *)
(*                        Closed Notations on level 0                        *)
(* ========================================================================= *)

Notation "'pass'" := (USugar (UConstBits Ob)) (in custom koika).
Notation "'magic'" := (USugar UErrorInAst) (in custom koika).

Notation "'fail'"            := (UFail (bits_t 0)) (in custom koika, format "fail").
Notation "'fail' '(' t ')'"  := (UFail (bits_t t)) (in custom koika, t constr, format "fail ( t )").
Notation "'fail' '@(' t ')'" := (UFail t         ) (in custom koika, t constr, format "fail @( t )").


Notation "'read0' '(' reg ')' "           := (URead P0 reg)        (in custom koika, reg constr, format "read0 ( reg )").
Notation "'read1' '(' reg ')' "           := (URead P1 reg)        (in custom koika, reg constr, format "read1 ( reg )").
Notation "'write0' '(' reg ',' value ')'" := (UWrite P0 reg value) (in custom koika, reg constr, format "write0 ( reg ,  value )").
Notation "'write1' '(' reg ',' value ')'" := (UWrite P1 reg value) (in custom koika, reg constr, format "write1 ( reg ,  value )").


Notation "'zeroExtend(' a ',' b ')'" :=  (UUnop (UBits1 (UZExtL b)) a) (in custom koika, b constr, format "'zeroExtend(' a ',' b ')'").
Notation "'sext(' a ',' b ')'"       :=  (UUnop (UBits1 (USExt  b)) a) (in custom koika, b constr, format "'sext(' a ',' b ')'").

Notation "'ignore(' a ')'"       :=  (UUnop (UConv     UIgnore) a) (in custom koika).
Notation "'pack(' a ')'"         :=  (UUnop (UConv       UPack) a) (in custom koika).
Notation "'unpack(' t ',' v ')'" :=  (UUnop (UConv (UUnpack t)) v) (in custom koika, t constr).

(* Deprecated *)
(* Notation "'call' instance method args" :=
  (USugar (UCallModule instance _ method args))
    (in custom koika at level 99, instance constr at level 0, method constr at level 0, args custom koika_args).
Notation "'funcall' method args" :=
  (USugar (UCallModule id _ method args))
    (in custom koika at level 98, method constr at level 0, args custom koika_args). *)
Notation "'extcall' method '(' arg ')'" :=
  (UExternalCall method arg)
    (in custom koika, method constr at level 0).
(* Notation "'call0' instance method " :=
  (USugar (UCallModule instance _ method nil))
    (in custom koika at level 98, instance constr at level 0, method constr).
Notation "'funcall0' method " :=
  (USugar (UCallModule id _ method nil))
    (in custom koika at level 98,  method constr at level 0). *)


Notation "'get' '(' v ',' f ')'"                   := (UUnop  (UStruct1 (UGetField f))           v) (in custom koika, f custom koika_var, format "'get' '(' v ','  f ')'").
Notation "'getbits' '(' t ',' v ',' f ')'"         := (UUnop  (UStruct1 (UGetFieldBits t f))     v) (in custom koika, f custom koika_var, t constr, format "'getbits' '(' t ','  v ','  f ')'").
Notation "'subst' '(' v ',' f ',' a ')'"           := (UBinop (UStruct2 (USubstField f))       v a) (in custom koika, f custom koika_var, format "'subst' '(' v ','  f ',' a ')'").
Notation "'substbits' '(' t ',' v ',' f ',' a ')'" := (UBinop (UStruct2 (USubstFieldBits t f)) v a) (in custom koika, f custom koika_var, t constr, format "'substbits' '(' t ','  v ','  f ',' a ')'").

Notation "'aref' '(' v ',' f ')'"                   := (UUnop  (UArray1 (UGetElement f))           v) (in custom koika, f constr, format "'aref' '(' v ','  f ')'").
Notation "'arefbits' '(' t ',' v ',' f ')'"         := (UUnop  (UArray1 (UGetElementBits t f))     v) (in custom koika, f constr, t constr, format "'arefbits' '(' t ','  v ','  f ')'").
Notation "'asubst' '(' v ',' f ',' a ')'"           := (UBinop (UArray2 (USubstElement f))       v a) (in custom koika, f constr, format "'asubst' '(' v ','  f ',' a ')'").
Notation "'asubstbits' '(' t ',' v ',' f ',' a ')'" := (UBinop (UArray2 (USubstElementBits t f)) v a) (in custom koika, f constr, t constr, format "'asubstbits' '(' t ','  v ','  f ',' a ')'").

(* Koika_branches *)
Declare Custom Entry koika_branches.
Notation "x '=>' a "     := [(x,a)]        (in custom koika_branches at level 0, x custom koika at level 200, a custom koika at level 200).
Notation "arg1 '|' arg2" := (arg1 ++ arg2) (in custom koika_branches at level 1, format "'[v' arg1 ']' '/' '|'  '[v' arg2 ']'").

(* TODO total match -> maybe for enums? *)
Notation "'match' var 'with' '|' branches 'return' 'default' ':' default 'end'" :=
  (USugar (USwitch var default branches))
    (in custom koika, branches custom koika_branches,
        format "'match'  var  'with' '/' '[v'  '|'  branches '/' 'return'  'default' ':' default ']' 'end'").

(* ========================================================================= *)
(*                            scheduler notations                            *)
(* ========================================================================= *)

Notation "r '|>' s" :=
  (Cons r s)
    (at level 99, s at level 99, right associativity).
Notation "'done'" :=
  Done (at level 99).

Module Type Tests.
  Parameter pos_t : Type.
  Parameter fn_name_t : Type.
  Parameter reg_t : Type.
  Parameter ext_fn_t : Type.
  Notation uaction reg_t := (uaction pos_t string fn_name_t reg_t ext_fn_t).
  Definition test_2 : uaction reg_t := {{ yo; yoyo }}.
  Definition test_3 : uaction reg_t := {{ set  yoyo := `UVar "magic" : uaction reg_t`  }}.
  Definition test_1 : uaction reg_t := {{ let yoyo := fail(2) in magic }}.
  Definition test_1' : uaction reg_t := {{ let yoyo := fail(2) in yoyo }}.
  Definition test_2' : uaction reg_t := {{ magic; magic }}.
  Definition test_3' : uaction reg_t := {{ set yoyo := magic ; magic }}.
  Definition test_4 : uaction reg_t := {{ magic ; set yoyo := magic }}.
  Definition test_5 : uaction reg_t := {{ let yoyo := set yoyo := magic in magic }}.
  Definition test_6 : uaction reg_t := {{ let yoyo := set yoyo := magic; magic in magic;magic }}.
  Definition test_7 : uaction reg_t := {{ (let yoyo := (set yoyo := magic); magic in magic;magic) }}.
  Definition test_8 : uaction reg_t := {{ (let yoyo := set yoyo := magic; magic in magic);magic }}.
  Inductive test : Set := |rData (n:nat).
  Axiom data0 : reg_t.
  Axiom data1 : reg_t.
  Definition test_9 : uaction reg_t := {{ read0(data0) }}.
  Definition test_10 : nat -> uaction test := (fun idx => {{ read0(rData idx) }}).
  Definition test_11 : uaction reg_t := {{ (let yoyo := read0(data0) in write0(data0, magic)); fail }}.
  Definition test_12 : uaction reg_t := {{ (let yoyo := if fail then read0(data0) else fail in write0(data0,magic));fail }}.
  Definition test_13 : uaction reg_t := {{ yoyo }}.
  Definition test_14 : uaction reg_t := {{ !yoyo && yoyo }}.
  Definition test_14' : uaction reg_t := {{ !(yoyo && yoyo) }}.
  Goal test_14 <> test_14'. compute; congruence. Qed.
  Definition test_15 : uaction reg_t := {{ yoyo && read0(data0) }}.
  Definition test_16 : uaction reg_t := {{ !read0(data1) && !read0(data1) }}.
  Definition test_17 : uaction reg_t := {{ !read0(data1) && magic}}.
  Definition test_18 : uaction reg_t := {{ !read0(data1) && Yoyo }}.
  Definition test_19 : uaction reg_t := {{ yoy [ oio && ab ] && Ob~1~0 }}.
  Definition test_20 : uaction reg_t := {{ yoyo [ magic :+ 3 ] && yoyo }}.
  Definition test_20' : uaction reg_t := {{ (yoyo [ magic :+ 3]  ++ yoyo) && yoyo }}.
  Definition test_20'' : uaction reg_t := {{ ( yoyo [ magic :+ 3 ] ++ yoyo ++bla) && yoyo }}.
  Notation UInternalFunction :=
    (UInternalFunction pos_t string string reg_t ext_fn_t).
  Definition test_23 : UInternalFunction string string (uaction reg_t) := {{ fun test (arg1 : (bits_t 3)) (arg2 : bits_t 2) : bits_t 4 => magic }}.
  Definition test_24 : nat -> UInternalFunction string string (uaction reg_t) :=  (fun sz => {{ fun test (arg1 : bits_t sz) (arg1 : bits_t sz) : bits_t sz  => magic}}).
  Definition test_25 : nat -> UInternalFunction string string (uaction reg_t) := (fun sz => {{fun test (arg1 : bits_t sz ) : bits_t sz => let oo := magic >> magic in magic}}).
  Definition test_26 : nat -> UInternalFunction string string (uaction reg_t) := (fun sz => {{ fun test () : bits_t sz  => magic }}).
  Definition test_27 : uaction reg_t := {{
    if (!read0(data0)) then
      write0(data0, Ob~1);
      let yo := if (dlk == Ob~1 ) then bla else yoyo || foo
      in
      write0(data0, Ob~1)
    else
      read0(data0);
    fail
  }}.
  Definition test_28 : uaction reg_t :=  {{
    match var with
    | magic => magic
    return default: magic
    end
  }}.

  Definition mem_req :=
    {| struct_name := "mem_req";
       struct_fields := cons ("type", bits_t 1) nil |}.

  Definition test_30'' : uaction reg_t := {{
    struct mem_req { foo := upu[#(Bits.of_nat 3 0) :+ 2] ;
                     bar := |32`d98| }
  }}.

  Definition test_31'' : uaction reg_t := {{
    pack(a)
  }}.

  Definition test_31' : uaction reg_t := {{
    let a := struct mem_req { foo := upu[#(Bits.of_nat 3 0) :+ 2] ;
                              bar := |32`d98| } in
    unpack(struct_t mem_req, pack(a))
  }}.
  
  
  Notation "'[|' a '=koika=' b '|]'" := ((a : uaction reg_t) = (b : uaction reg_t)) (a custom koika, b custom koika).

  Definition short_get_syntax :
  [|
    get(a, some_field)
  =koika=
    a.[some_field]
  |] := eq_refl.

  Definition num_test_b_1 : [| "01101":b     =koika= Ob~0~1~1~0~1 |] := eq_refl.
  Definition num_test_b_2 : [| 0b"00011"     =koika= Ob~0~0~0~1~1 |] := eq_refl.
  Definition num_test_b_3 : [| "11":b5       =koika= Ob~0~0~0~1~1 |] := eq_refl.
  Definition num_test_b_4 : [| 0b"10"5       =koika= Ob~0~0~0~1~0 |] := eq_refl.
  Definition num_test_b_5 : [| 0b"10010110"3 =koika= Ob~1~1~0     |] := eq_refl.
  Definition num_test_b_6 : [| "011_01":b    =koika= Ob~0~1~1~0~1 |] := eq_refl.
  Definition num_test_b_7 : [| "0'11'01":b   =koika= Ob~0~1~1~0~1 |] := eq_refl.
  Fail Definition num_test_b_6  := {{ 0b"102"  }} : uaction reg_t.
  Fail Definition num_test_b_7  := {{ 0b"10f"6 }} : uaction reg_t.
  Fail Definition num_test_b_8  := {{ "f0":b5  }} : uaction reg_t.
  Fail Definition num_test_b_9  := {{ "f0":b   }} : uaction reg_t.
  Fail Definition num_test_b_10 := {{ "":b     }} : uaction reg_t.

  Definition num_test_o_1 : [| "330":o   =koika= Ob~0~1~1~0~1~1~0~0~0     |] := eq_refl.
  Definition num_test_o_2 : [| "070":o9  =koika= Ob~0~0~0~1~1~1~0~0~0     |] := eq_refl.
  Definition num_test_o_3 : [| 0o"000"   =koika= Ob~0~0~0~0~0~0~0~0~0     |] := eq_refl.
  Definition num_test_o_4 : [| 0o"750"11 =koika= Ob~0~0~1~1~1~1~0~1~0~0~0 |] := eq_refl.
  Definition num_test_o_5 : [| 0o"751"3  =koika= Ob~0~0~1                 |] := eq_refl.
  Fail Definition num_test_o_6  := {{ 0o"108"   }} : uaction reg_t.
  Fail Definition num_test_o_7  := {{ 0o"080"10 }} : uaction reg_t.
  Fail Definition num_test_o_8  := {{ "f00":o10 }} : uaction reg_t.
  Fail Definition num_test_o_9  := {{ "00f":o5  }} : uaction reg_t.
  Fail Definition num_test_o_10 := {{ "":o      }} : uaction reg_t.

  Definition num_test_d_1 : [| "33":d    =koika= Ob~1~0~0~0~0~1           |] := eq_refl.
  Definition num_test_d_2 : [| "33":d9   =koika= Ob~0~0~0~1~0~0~0~0~1     |] := eq_refl.
  Definition num_test_d_3 : [| "070":d9  =koika= Ob~0~0~1~0~0~0~1~1~0     |] := eq_refl.
  Definition num_test_d_4 : [| 0d"070"   =koika= Ob~1~0~0~0~1~1~0         |] := eq_refl.
  Definition num_test_d_5 : [| 0d"198"11 =koika= Ob~0~0~0~1~1~0~0~0~1~1~0 |] := eq_refl.
  Definition num_test_d_6 : [| 0d"15"3   =koika= Ob~1~1~1                 |] := eq_refl.
  Fail Definition num_test_d_7  := {{ 0d"1a0"   }} : uaction reg_t.
  Fail Definition num_test_d_8  := {{ 0d"0z0"10 }} : uaction reg_t.
  Fail Definition num_test_d_9  := {{ "f00":d10 }} : uaction reg_t.
  Fail Definition num_test_d_10 := {{ "00f":d5  }} : uaction reg_t.
  Fail Definition num_test_d_11 := {{ "":d      }} : uaction reg_t.

  Definition num_test_h_1 : [| "fa":h    =koika= Ob~1~1~1~1~1~0~1~0         |] := eq_refl.
  Definition num_test_h_2 : [| "bb":h9   =koika= Ob~0~1~0~1~1~1~0~1~1       |] := eq_refl.
  Definition num_test_h_3 : [| "014":h   =koika= Ob~0~0~0~0~0~0~0~1~0~1~0~0 |] := eq_refl.
  Definition num_test_h_4 : [| 0x"070"   =koika= Ob~0~0~0~0~0~1~1~1~0~0~0~0 |] := eq_refl.
  Definition num_test_h_5 : [| 0x"198"11 =koika= Ob~0~0~1~1~0~0~1~1~0~0~0   |] := eq_refl.
  Definition num_test_h_6 : [| 0x"1d"3   =koika= Ob~1~0~1                   |] := eq_refl.
  Definition num_test_h_7 : [| "f_a":h   =koika= Ob~1~1~1~1~1~0~1~0         |] := eq_refl.
  Fail Definition num_test_h_7  := {{ 0x"1h0"   }} : uaction reg_t.
  Fail Definition num_test_h_8  := {{ 0x"0z0"10 }} : uaction reg_t.
  Fail Definition num_test_h_9  := {{ "g00":h10 }} : uaction reg_t.
  Fail Definition num_test_h_10 := {{ "00k":h5  }} : uaction reg_t.
  Fail Definition num_test_h_11 := {{ "":h      }} : uaction reg_t.
End Tests.
