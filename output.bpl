
// ** Expanded prelude

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Basic theory for vectors using arrays. This version of vectors is not extensional.

type {:datatype} Vec _;

function {:constructor} Vec<T>(v: [int]T, l: int): Vec T;

function {:builtin "MapConst"} MapConstVec<T>(T): [int]T;
function DefaultVecElem<T>(): T;
function {:inline} DefaultVecMap<T>(): [int]T { MapConstVec(DefaultVecElem()) }

function {:inline} EmptyVec<T>(): Vec T {
    Vec(DefaultVecMap(), 0)
}

function {:inline} MakeVec1<T>(v: T): Vec T {
    Vec(DefaultVecMap()[0 := v], 1)
}

function {:inline} MakeVec2<T>(v1: T, v2: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2], 2)
}

function {:inline} MakeVec3<T>(v1: T, v2: T, v3: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2][2 := v3], 3)
}

function {:inline} MakeVec4<T>(v1: T, v2: T, v3: T, v4: T): Vec T {
    Vec(DefaultVecMap()[0 := v1][1 := v2][2 := v3][3 := v4], 4)
}

function {:inline} ExtendVec<T>(v: Vec T, elem: T): Vec T {
    (var l := l#Vec(v);
    Vec(v#Vec(v)[l := elem], l + 1))
}

function {:inline} ReadVec<T>(v: Vec T, i: int): T {
    v#Vec(v)[i]
}

function {:inline} LenVec<T>(v: Vec T): int {
    l#Vec(v)
}

function {:inline} IsEmptyVec<T>(v: Vec T): bool {
    l#Vec(v) == 0
}

function {:inline} RemoveVec<T>(v: Vec T): Vec T {
    (var l := l#Vec(v) - 1;
    Vec(v#Vec(v)[l := DefaultVecElem()], l))
}

function {:inline} RemoveAtVec<T>(v: Vec T, i: int): Vec T {
    (var l := l#Vec(v) - 1;
    Vec(
        (lambda j: int ::
           if j >= 0 && j < l then
               if j < i then v#Vec(v)[j] else v#Vec(v)[j+1]
           else DefaultVecElem()),
        l))
}

function {:inline} InsertAtVec<T>(v: Vec T, i: int, elem: T): Vec T {
    (var l := l#Vec(v) + 1;
    Vec(
        (lambda j: int ::
         if j >= 0 && j < l then
           if j < i then v#Vec(v)[j]
           else if j > i then v#Vec(v)[j-1] else elem
         else DefaultVecElem()),
        l))
}

function {:inline} ConcatVec<T>(v1: Vec T, v2: Vec T): Vec T {
    (var l1, m1, l2, m2 := l#Vec(v1), v#Vec(v1), l#Vec(v2), v#Vec(v2);
    Vec(
        (lambda i: int ::
          if i >= 0 && i < l1 + l2 then
            if i < l1 then m1[i] else m2[i - l1]
          else DefaultVecElem()),
        l1 + l2))
}

function {:inline} ReverseVec<T>(v: Vec T): Vec T {
    (var l := l#Vec(v);
    Vec(
        (lambda i: int :: if 0 <= i && i < l then v#Vec(v)[l - i - 1] else DefaultVecElem()),
        l))
}

function {:inline} SliceVec<T>(v: Vec T, i: int, j: int): Vec T {
    (var m := v#Vec(v);
    Vec(
        (lambda k:int ::
          if 0 <= k && k < j - i then
            m[i + k]
          else
            DefaultVecElem()),
        (if j - i < 0 then 0 else j - i)))
}


function {:inline} UpdateVec<T>(v: Vec T, i: int, elem: T): Vec T {
    Vec(v#Vec(v)[i := elem], l#Vec(v))
}

function {:inline} SwapVec<T>(v: Vec T, i: int, j: int): Vec T {
    (var m := v#Vec(v);
    Vec(m[i := m[j]][j := m[i]], l#Vec(v)))
}

function {:inline} ContainsVec<T>(v: Vec T, e: T): bool {
    (var l := l#Vec(v);
    (exists i: int :: InRangeVec(v, i) && v#Vec(v)[i] == e))
}

function IndexOfVec<T>(v: Vec T, e: T): int;
axiom {:ctor "Vec"} (forall<T> v: Vec T, e: T :: {IndexOfVec(v, e)}
    (var i := IndexOfVec(v,e);
     if (!ContainsVec(v, e)) then i == -1
     else InRangeVec(v, i) && ReadVec(v, i) == e &&
        (forall j: int :: j >= 0 && j < i ==> ReadVec(v, j) != e)));

// This function should stay non-inlined as it guards many quantifiers
// over vectors. It appears important to have this uninterpreted for
// quantifier triggering.
function InRangeVec<T>(v: Vec T, i: int): bool {
    i >= 0 && i < LenVec(v)
}

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Boogie model for multisets, based on Boogie arrays. This theory assumes extensional equality for element types.

type {:datatype} Multiset _;
function {:constructor} Multiset<T>(v: [T]int, l: int): Multiset T;

function {:builtin "MapConst"} MapConstMultiset<T>(l: int): [T]int;

function {:inline} EmptyMultiset<T>(): Multiset T {
    Multiset(MapConstMultiset(0), 0)
}

function {:inline} LenMultiset<T>(s: Multiset T): int {
    l#Multiset(s)
}

function {:inline} ExtendMultiset<T>(s: Multiset T, v: T): Multiset T {
    (var len := l#Multiset(s);
    (var cnt := v#Multiset(s)[v];
    Multiset(v#Multiset(s)[v := (cnt + 1)], len + 1)))
}

// This function returns (s1 - s2). This function assumes that s2 is a subset of s1.
function {:inline} SubtractMultiset<T>(s1: Multiset T, s2: Multiset T): Multiset T {
    (var len1 := l#Multiset(s1);
    (var len2 := l#Multiset(s2);
    Multiset((lambda v:T :: v#Multiset(s1)[v]-v#Multiset(s2)[v]), len1-len2)))
}

function {:inline} IsEmptyMultiset<T>(s: Multiset T): bool {
    (l#Multiset(s) == 0) &&
    (forall v: T :: v#Multiset(s)[v] == 0)
}

function {:inline} IsSubsetMultiset<T>(s1: Multiset T, s2: Multiset T): bool {
    (l#Multiset(s1) <= l#Multiset(s2)) &&
    (forall v: T :: v#Multiset(s1)[v] <= v#Multiset(s2)[v])
}

function {:inline} ContainsMultiset<T>(s: Multiset T, v: T): bool {
    v#Multiset(s)[v] > 0
}

// Copyright (c) The Diem Core Contributors
// Copyright (c) The Move Contributors
// SPDX-License-Identifier: Apache-2.0

// Theory for tables.

type {:datatype} Table _ _;

// v is the SMT array holding the key-value assignment. e is an array which
// independently determines whether a key is valid or not. l is the length.
//
// Note that even though the program cannot reflect over existence of a key,
// we want the specification to be able to do this, so it can express
// verification conditions like "key has been inserted".
function {:constructor} Table<K, V>(v: [K]V, e: [K]bool, l: int): Table K V;

// Functions for default SMT arrays. For the table values, we don't care and
// use an uninterpreted function.
function DefaultTableArray<K, V>(): [K]V;
function DefaultTableKeyExistsArray<K>(): [K]bool;
axiom DefaultTableKeyExistsArray() == (lambda i: int :: false);

function {:inline} EmptyTable<K, V>(): Table K V {
    Table(DefaultTableArray(), DefaultTableKeyExistsArray(), 0)
}

function {:inline} GetTable<K,V>(t: Table K V, k: K): V {
    // Notice we do not check whether key is in the table. The result is undetermined if it is not.
    v#Table(t)[k]
}

function {:inline} LenTable<K,V>(t: Table K V): int {
    l#Table(t)
}


function {:inline} ContainsTable<K,V>(t: Table K V, k: K): bool {
    e#Table(t)[k]
}

function {:inline} UpdateTable<K,V>(t: Table K V, k: K, v: V): Table K V {
    Table(v#Table(t)[k := v], e#Table(t), l#Table(t))
}

function {:inline} AddTable<K,V>(t: Table K V, k: K, v: V): Table K V {
    // This function has an undetermined result if the key is already in the table
    // (all specification functions have this "partial definiteness" behavior). Thus we can
    // just increment the length.
    Table(v#Table(t)[k := v], e#Table(t)[k := true], l#Table(t) + 1)
}

function {:inline} RemoveTable<K,V>(t: Table K V, k: K): Table K V {
    // Similar as above, we only need to consider the case where the key is in the table.
    Table(v#Table(t), e#Table(t)[k := false], l#Table(t) - 1)
}

axiom {:ctor "Table"} (forall<K,V> t: Table K V :: {LenTable(t)}
    (exists k: K :: {ContainsTable(t, k)} ContainsTable(t, k)) ==> LenTable(t) >= 1
);
// TODO: we might want to encoder a stronger property that the length of table
// must be more than N given a set of N items. Currently we don't see a need here
// and the above axiom seems to be sufficient.


// ============================================================================================
// Primitive Types

const $MAX_U8: int;
axiom $MAX_U8 == 255;
const $MAX_U16: int;
axiom $MAX_U16 == 65535;
const $MAX_U32: int;
axiom $MAX_U32 == 4294967295;
const $MAX_U64: int;
axiom $MAX_U64 == 18446744073709551615;
const $MAX_U128: int;
axiom $MAX_U128 == 340282366920938463463374607431768211455;
const $MAX_U256: int;
axiom $MAX_U256 == 115792089237316195423570985008687907853269984665640564039457584007913129639935;

// Templates for bitvector operations

function {:bvbuiltin "bvand"} $And'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvor"} $Or'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvxor"} $Xor'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvadd"} $Add'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvsub"} $Sub'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvmul"} $Mul'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvudiv"} $Div'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvurem"} $Mod'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvshl"} $Shl'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvlshr"} $Shr'Bv8'(bv8,bv8) returns(bv8);
function {:bvbuiltin "bvult"} $Lt'Bv8'(bv8,bv8) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv8'(bv8,bv8) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv8'(bv8,bv8) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv8'(bv8,bv8) returns(bool);

procedure {:inline 1} $AddBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Lt'Bv8'($Add'Bv8'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv8'(src1, src2);
}

procedure {:inline 1} $AddBv8_unchecked(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $Add'Bv8'(src1, src2);
}

procedure {:inline 1} $SubBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Lt'Bv8'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv8'(src1, src2);
}

procedure {:inline 1} $MulBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Lt'Bv8'($Mul'Bv8'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv8'(src1, src2);
}

procedure {:inline 1} $DivBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if (src2 == 0bv8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv8'(src1, src2);
}

procedure {:inline 1} $ModBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if (src2 == 0bv8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv8'(src1, src2);
}

procedure {:inline 1} $AndBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $And'Bv8'(src1,src2);
}

procedure {:inline 1} $OrBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $Or'Bv8'(src1,src2);
}

procedure {:inline 1} $XorBv8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    dst := $Xor'Bv8'(src1,src2);
}

procedure {:inline 1} $LtBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Lt'Bv8'(src1,src2);
}

procedure {:inline 1} $LeBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Le'Bv8'(src1,src2);
}

procedure {:inline 1} $GtBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Gt'Bv8'(src1,src2);
}

procedure {:inline 1} $GeBv8(src1: bv8, src2: bv8) returns (dst: bool)
{
    dst := $Ge'Bv8'(src1,src2);
}

function $IsValid'bv8'(v: bv8): bool {
  $Ge'Bv8'(v,0bv8) && $Le'Bv8'(v,255bv8)
}

function {:inline} $IsEqual'bv8'(x: bv8, y: bv8): bool {
    x == y
}

procedure {:inline 1} $int2bv8(src: int) returns (dst: bv8)
{
    if (src > 255) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.8(src);
}

procedure {:inline 1} $bv2int8(src: bv8) returns (dst: int)
{
    dst := $bv2int.8(src);
}

function {:builtin "(_ int2bv 8)"} $int2bv.8(i: int) returns (bv8);
function {:builtin "bv2nat"} $bv2int.8(i: bv8) returns (int);

function {:bvbuiltin "bvand"} $And'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvor"} $Or'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvxor"} $Xor'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvadd"} $Add'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvsub"} $Sub'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvmul"} $Mul'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvudiv"} $Div'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvurem"} $Mod'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvshl"} $Shl'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvlshr"} $Shr'Bv16'(bv16,bv16) returns(bv16);
function {:bvbuiltin "bvult"} $Lt'Bv16'(bv16,bv16) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv16'(bv16,bv16) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv16'(bv16,bv16) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv16'(bv16,bv16) returns(bool);

procedure {:inline 1} $AddBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Lt'Bv16'($Add'Bv16'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv16'(src1, src2);
}

procedure {:inline 1} $AddBv16_unchecked(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $Add'Bv16'(src1, src2);
}

procedure {:inline 1} $SubBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Lt'Bv16'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv16'(src1, src2);
}

procedure {:inline 1} $MulBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Lt'Bv16'($Mul'Bv16'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv16'(src1, src2);
}

procedure {:inline 1} $DivBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if (src2 == 0bv16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv16'(src1, src2);
}

procedure {:inline 1} $ModBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if (src2 == 0bv16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv16'(src1, src2);
}

procedure {:inline 1} $AndBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $And'Bv16'(src1,src2);
}

procedure {:inline 1} $OrBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $Or'Bv16'(src1,src2);
}

procedure {:inline 1} $XorBv16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    dst := $Xor'Bv16'(src1,src2);
}

procedure {:inline 1} $LtBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Lt'Bv16'(src1,src2);
}

procedure {:inline 1} $LeBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Le'Bv16'(src1,src2);
}

procedure {:inline 1} $GtBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Gt'Bv16'(src1,src2);
}

procedure {:inline 1} $GeBv16(src1: bv16, src2: bv16) returns (dst: bool)
{
    dst := $Ge'Bv16'(src1,src2);
}

function $IsValid'bv16'(v: bv16): bool {
  $Ge'Bv16'(v,0bv16) && $Le'Bv16'(v,65535bv16)
}

function {:inline} $IsEqual'bv16'(x: bv16, y: bv16): bool {
    x == y
}

procedure {:inline 1} $int2bv16(src: int) returns (dst: bv16)
{
    if (src > 65535) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.16(src);
}

procedure {:inline 1} $bv2int16(src: bv16) returns (dst: int)
{
    dst := $bv2int.16(src);
}

function {:builtin "(_ int2bv 16)"} $int2bv.16(i: int) returns (bv16);
function {:builtin "bv2nat"} $bv2int.16(i: bv16) returns (int);

function {:bvbuiltin "bvand"} $And'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvor"} $Or'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvxor"} $Xor'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvadd"} $Add'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvsub"} $Sub'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvmul"} $Mul'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvudiv"} $Div'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvurem"} $Mod'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvshl"} $Shl'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvlshr"} $Shr'Bv32'(bv32,bv32) returns(bv32);
function {:bvbuiltin "bvult"} $Lt'Bv32'(bv32,bv32) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv32'(bv32,bv32) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv32'(bv32,bv32) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv32'(bv32,bv32) returns(bool);

procedure {:inline 1} $AddBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Lt'Bv32'($Add'Bv32'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv32'(src1, src2);
}

procedure {:inline 1} $AddBv32_unchecked(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $Add'Bv32'(src1, src2);
}

procedure {:inline 1} $SubBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Lt'Bv32'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv32'(src1, src2);
}

procedure {:inline 1} $MulBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Lt'Bv32'($Mul'Bv32'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv32'(src1, src2);
}

procedure {:inline 1} $DivBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if (src2 == 0bv32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv32'(src1, src2);
}

procedure {:inline 1} $ModBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if (src2 == 0bv32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv32'(src1, src2);
}

procedure {:inline 1} $AndBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $And'Bv32'(src1,src2);
}

procedure {:inline 1} $OrBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $Or'Bv32'(src1,src2);
}

procedure {:inline 1} $XorBv32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    dst := $Xor'Bv32'(src1,src2);
}

procedure {:inline 1} $LtBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Lt'Bv32'(src1,src2);
}

procedure {:inline 1} $LeBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Le'Bv32'(src1,src2);
}

procedure {:inline 1} $GtBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Gt'Bv32'(src1,src2);
}

procedure {:inline 1} $GeBv32(src1: bv32, src2: bv32) returns (dst: bool)
{
    dst := $Ge'Bv32'(src1,src2);
}

function $IsValid'bv32'(v: bv32): bool {
  $Ge'Bv32'(v,0bv32) && $Le'Bv32'(v,2147483647bv32)
}

function {:inline} $IsEqual'bv32'(x: bv32, y: bv32): bool {
    x == y
}

procedure {:inline 1} $int2bv32(src: int) returns (dst: bv32)
{
    if (src > 2147483647) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.32(src);
}

procedure {:inline 1} $bv2int32(src: bv32) returns (dst: int)
{
    dst := $bv2int.32(src);
}

function {:builtin "(_ int2bv 32)"} $int2bv.32(i: int) returns (bv32);
function {:builtin "bv2nat"} $bv2int.32(i: bv32) returns (int);

function {:bvbuiltin "bvand"} $And'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvor"} $Or'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvxor"} $Xor'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvadd"} $Add'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvsub"} $Sub'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvmul"} $Mul'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvudiv"} $Div'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvurem"} $Mod'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvshl"} $Shl'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvlshr"} $Shr'Bv64'(bv64,bv64) returns(bv64);
function {:bvbuiltin "bvult"} $Lt'Bv64'(bv64,bv64) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv64'(bv64,bv64) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv64'(bv64,bv64) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv64'(bv64,bv64) returns(bool);

procedure {:inline 1} $AddBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Lt'Bv64'($Add'Bv64'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv64'(src1, src2);
}

procedure {:inline 1} $AddBv64_unchecked(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $Add'Bv64'(src1, src2);
}

procedure {:inline 1} $SubBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Lt'Bv64'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv64'(src1, src2);
}

procedure {:inline 1} $MulBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Lt'Bv64'($Mul'Bv64'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv64'(src1, src2);
}

procedure {:inline 1} $DivBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if (src2 == 0bv64) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv64'(src1, src2);
}

procedure {:inline 1} $ModBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if (src2 == 0bv64) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv64'(src1, src2);
}

procedure {:inline 1} $AndBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $And'Bv64'(src1,src2);
}

procedure {:inline 1} $OrBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $Or'Bv64'(src1,src2);
}

procedure {:inline 1} $XorBv64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    dst := $Xor'Bv64'(src1,src2);
}

procedure {:inline 1} $LtBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Lt'Bv64'(src1,src2);
}

procedure {:inline 1} $LeBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Le'Bv64'(src1,src2);
}

procedure {:inline 1} $GtBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Gt'Bv64'(src1,src2);
}

procedure {:inline 1} $GeBv64(src1: bv64, src2: bv64) returns (dst: bool)
{
    dst := $Ge'Bv64'(src1,src2);
}

function $IsValid'bv64'(v: bv64): bool {
  $Ge'Bv64'(v,0bv64) && $Le'Bv64'(v,18446744073709551615bv64)
}

function {:inline} $IsEqual'bv64'(x: bv64, y: bv64): bool {
    x == y
}

procedure {:inline 1} $int2bv64(src: int) returns (dst: bv64)
{
    if (src > 18446744073709551615) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.64(src);
}

procedure {:inline 1} $bv2int64(src: bv64) returns (dst: int)
{
    dst := $bv2int.64(src);
}

function {:builtin "(_ int2bv 64)"} $int2bv.64(i: int) returns (bv64);
function {:builtin "bv2nat"} $bv2int.64(i: bv64) returns (int);

function {:bvbuiltin "bvand"} $And'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvor"} $Or'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvxor"} $Xor'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvadd"} $Add'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvsub"} $Sub'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvmul"} $Mul'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvudiv"} $Div'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvurem"} $Mod'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvshl"} $Shl'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvlshr"} $Shr'Bv128'(bv128,bv128) returns(bv128);
function {:bvbuiltin "bvult"} $Lt'Bv128'(bv128,bv128) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv128'(bv128,bv128) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv128'(bv128,bv128) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv128'(bv128,bv128) returns(bool);

procedure {:inline 1} $AddBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Lt'Bv128'($Add'Bv128'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv128'(src1, src2);
}

procedure {:inline 1} $AddBv128_unchecked(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $Add'Bv128'(src1, src2);
}

procedure {:inline 1} $SubBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Lt'Bv128'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv128'(src1, src2);
}

procedure {:inline 1} $MulBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Lt'Bv128'($Mul'Bv128'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv128'(src1, src2);
}

procedure {:inline 1} $DivBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if (src2 == 0bv128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv128'(src1, src2);
}

procedure {:inline 1} $ModBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if (src2 == 0bv128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv128'(src1, src2);
}

procedure {:inline 1} $AndBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $And'Bv128'(src1,src2);
}

procedure {:inline 1} $OrBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $Or'Bv128'(src1,src2);
}

procedure {:inline 1} $XorBv128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    dst := $Xor'Bv128'(src1,src2);
}

procedure {:inline 1} $LtBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Lt'Bv128'(src1,src2);
}

procedure {:inline 1} $LeBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Le'Bv128'(src1,src2);
}

procedure {:inline 1} $GtBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Gt'Bv128'(src1,src2);
}

procedure {:inline 1} $GeBv128(src1: bv128, src2: bv128) returns (dst: bool)
{
    dst := $Ge'Bv128'(src1,src2);
}

function $IsValid'bv128'(v: bv128): bool {
  $Ge'Bv128'(v,0bv128) && $Le'Bv128'(v,340282366920938463463374607431768211455bv128)
}

function {:inline} $IsEqual'bv128'(x: bv128, y: bv128): bool {
    x == y
}

procedure {:inline 1} $int2bv128(src: int) returns (dst: bv128)
{
    if (src > 340282366920938463463374607431768211455) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.128(src);
}

procedure {:inline 1} $bv2int128(src: bv128) returns (dst: int)
{
    dst := $bv2int.128(src);
}

function {:builtin "(_ int2bv 128)"} $int2bv.128(i: int) returns (bv128);
function {:builtin "bv2nat"} $bv2int.128(i: bv128) returns (int);

function {:bvbuiltin "bvand"} $And'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvor"} $Or'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvxor"} $Xor'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvadd"} $Add'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvsub"} $Sub'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvmul"} $Mul'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvudiv"} $Div'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvurem"} $Mod'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvshl"} $Shl'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvlshr"} $Shr'Bv256'(bv256,bv256) returns(bv256);
function {:bvbuiltin "bvult"} $Lt'Bv256'(bv256,bv256) returns(bool);
function {:bvbuiltin "bvule"} $Le'Bv256'(bv256,bv256) returns(bool);
function {:bvbuiltin "bvugt"} $Gt'Bv256'(bv256,bv256) returns(bool);
function {:bvbuiltin "bvuge"} $Ge'Bv256'(bv256,bv256) returns(bool);

procedure {:inline 1} $AddBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Lt'Bv256'($Add'Bv256'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Add'Bv256'(src1, src2);
}

procedure {:inline 1} $AddBv256_unchecked(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $Add'Bv256'(src1, src2);
}

procedure {:inline 1} $SubBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Lt'Bv256'(src1, src2)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Sub'Bv256'(src1, src2);
}

procedure {:inline 1} $MulBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Lt'Bv256'($Mul'Bv256'(src1, src2), src1)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mul'Bv256'(src1, src2);
}

procedure {:inline 1} $DivBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if (src2 == 0bv256) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Div'Bv256'(src1, src2);
}

procedure {:inline 1} $ModBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if (src2 == 0bv256) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mod'Bv256'(src1, src2);
}

procedure {:inline 1} $AndBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $And'Bv256'(src1,src2);
}

procedure {:inline 1} $OrBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $Or'Bv256'(src1,src2);
}

procedure {:inline 1} $XorBv256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    dst := $Xor'Bv256'(src1,src2);
}

procedure {:inline 1} $LtBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Lt'Bv256'(src1,src2);
}

procedure {:inline 1} $LeBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Le'Bv256'(src1,src2);
}

procedure {:inline 1} $GtBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Gt'Bv256'(src1,src2);
}

procedure {:inline 1} $GeBv256(src1: bv256, src2: bv256) returns (dst: bool)
{
    dst := $Ge'Bv256'(src1,src2);
}

function $IsValid'bv256'(v: bv256): bool {
  $Ge'Bv256'(v,0bv256) && $Le'Bv256'(v,115792089237316195423570985008687907853269984665640564039457584007913129639935bv256)
}

function {:inline} $IsEqual'bv256'(x: bv256, y: bv256): bool {
    x == y
}

procedure {:inline 1} $int2bv256(src: int) returns (dst: bv256)
{
    if (src > 115792089237316195423570985008687907853269984665640564039457584007913129639935) {
        call $ExecFailureAbort();
        return;
    }
    dst := $int2bv.256(src);
}

procedure {:inline 1} $bv2int256(src: bv256) returns (dst: int)
{
    dst := $bv2int.256(src);
}

function {:builtin "(_ int2bv 256)"} $int2bv.256(i: int) returns (bv256);
function {:builtin "bv2nat"} $bv2int.256(i: bv256) returns (int);

type {:datatype} $Range;
function {:constructor} $Range(lb: int, ub: int): $Range;

function {:inline} $IsValid'bool'(v: bool): bool {
  true
}

function $IsValid'u8'(v: int): bool {
  v >= 0 && v <= $MAX_U8
}

function $IsValid'u16'(v: int): bool {
  v >= 0 && v <= $MAX_U16
}

function $IsValid'u32'(v: int): bool {
  v >= 0 && v <= $MAX_U32
}

function $IsValid'u64'(v: int): bool {
  v >= 0 && v <= $MAX_U64
}

function $IsValid'u128'(v: int): bool {
  v >= 0 && v <= $MAX_U128
}

function $IsValid'u256'(v: int): bool {
  v >= 0 && v <= $MAX_U256
}

function $IsValid'num'(v: int): bool {
  true
}

function $IsValid'address'(v: int): bool {
  // TODO: restrict max to representable addresses?
  v >= 0
}

function {:inline} $IsValidRange(r: $Range): bool {
   $IsValid'u64'(lb#$Range(r)) &&  $IsValid'u64'(ub#$Range(r))
}

// Intentionally not inlined so it serves as a trigger in quantifiers.
function $InRange(r: $Range, i: int): bool {
   lb#$Range(r) <= i && i < ub#$Range(r)
}


function {:inline} $IsEqual'u8'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u16'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u32'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u64'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u128'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'u256'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'num'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'address'(x: int, y: int): bool {
    x == y
}

function {:inline} $IsEqual'bool'(x: bool, y: bool): bool {
    x == y
}

// ============================================================================================
// Memory

type {:datatype} $Location;

// A global resource location within the statically known resource type's memory,
// where `a` is an address.
function {:constructor} $Global(a: int): $Location;

// A local location. `i` is the unique index of the local.
function {:constructor} $Local(i: int): $Location;

// The location of a reference outside of the verification scope, for example, a `&mut` parameter
// of the function being verified. References with these locations don't need to be written back
// when mutation ends.
function {:constructor} $Param(i: int): $Location;

// The location of an uninitialized mutation. Using this to make sure that the location
// will not be equal to any valid mutation locations, i.e., $Local, $Global, or $Param.
function {:constructor} $Uninitialized(): $Location;

// A mutable reference which also carries its current value. Since mutable references
// are single threaded in Move, we can keep them together and treat them as a value
// during mutation until the point they are stored back to their original location.
type {:datatype} $Mutation _;
function {:constructor} $Mutation<T>(l: $Location, p: Vec int, v: T): $Mutation T;

// Representation of memory for a given type.
type {:datatype} $Memory _;
function {:constructor} $Memory<T>(domain: [int]bool, contents: [int]T): $Memory T;

function {:builtin "MapConst"} $ConstMemoryDomain(v: bool): [int]bool;
function {:builtin "MapConst"} $ConstMemoryContent<T>(v: T): [int]T;
axiom $ConstMemoryDomain(false) == (lambda i: int :: false);
axiom $ConstMemoryDomain(true) == (lambda i: int :: true);


// Dereferences a mutation.
function {:inline} $Dereference<T>(ref: $Mutation T): T {
    v#$Mutation(ref)
}

// Update the value of a mutation.
function {:inline} $UpdateMutation<T>(m: $Mutation T, v: T): $Mutation T {
    $Mutation(l#$Mutation(m), p#$Mutation(m), v)
}

function {:inline} $ChildMutation<T1, T2>(m: $Mutation T1, offset: int, v: T2): $Mutation T2 {
    $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), offset), v)
}

// Return true if two mutations share the location and path
function {:inline} $IsSameMutation<T1, T2>(parent: $Mutation T1, child: $Mutation T2 ): bool {
    l#$Mutation(parent) == l#$Mutation(child) && p#$Mutation(parent) == p#$Mutation(child)
}

// Return true if the mutation is a parent of a child which was derived with the given edge offset. This
// is used to implement write-back choices.
function {:inline} $IsParentMutation<T1, T2>(parent: $Mutation T1, edge: int, child: $Mutation T2 ): bool {
    l#$Mutation(parent) == l#$Mutation(child) &&
    (var pp := p#$Mutation(parent);
    (var cp := p#$Mutation(child);
    (var pl := LenVec(pp);
    (var cl := LenVec(cp);
     cl == pl + 1 &&
     (forall i: int:: i >= 0 && i < pl ==> ReadVec(pp, i) ==  ReadVec(cp, i)) &&
     $EdgeMatches(ReadVec(cp, pl), edge)
    ))))
}

// Return true if the mutation is a parent of a child, for hyper edge.
function {:inline} $IsParentMutationHyper<T1, T2>(parent: $Mutation T1, hyper_edge: Vec int, child: $Mutation T2 ): bool {
    l#$Mutation(parent) == l#$Mutation(child) &&
    (var pp := p#$Mutation(parent);
    (var cp := p#$Mutation(child);
    (var pl := LenVec(pp);
    (var cl := LenVec(cp);
    (var el := LenVec(hyper_edge);
     cl == pl + el &&
     (forall i: int:: i >= 0 && i < pl ==> ReadVec(pp, i) == ReadVec(cp, i)) &&
     (forall i: int:: i >= 0 && i < el ==> $EdgeMatches(ReadVec(cp, pl + i), ReadVec(hyper_edge, i)))
    )))))
}

function {:inline} $EdgeMatches(edge: int, edge_pattern: int): bool {
    edge_pattern == -1 // wildcard
    || edge_pattern == edge
}



function {:inline} $SameLocation<T1, T2>(m1: $Mutation T1, m2: $Mutation T2): bool {
    l#$Mutation(m1) == l#$Mutation(m2)
}

function {:inline} $HasGlobalLocation<T>(m: $Mutation T): bool {
    is#$Global(l#$Mutation(m))
}

function {:inline} $HasLocalLocation<T>(m: $Mutation T, idx: int): bool {
    l#$Mutation(m) == $Local(idx)
}

function {:inline} $GlobalLocationAddress<T>(m: $Mutation T): int {
    a#$Global(l#$Mutation(m))
}



// Tests whether resource exists.
function {:inline} $ResourceExists<T>(m: $Memory T, addr: int): bool {
    domain#$Memory(m)[addr]
}

// Obtains Value of given resource.
function {:inline} $ResourceValue<T>(m: $Memory T, addr: int): T {
    contents#$Memory(m)[addr]
}

// Update resource.
function {:inline} $ResourceUpdate<T>(m: $Memory T, a: int, v: T): $Memory T {
    $Memory(domain#$Memory(m)[a := true], contents#$Memory(m)[a := v])
}

// Remove resource.
function {:inline} $ResourceRemove<T>(m: $Memory T, a: int): $Memory T {
    $Memory(domain#$Memory(m)[a := false], contents#$Memory(m))
}

// Copies resource from memory s to m.
function {:inline} $ResourceCopy<T>(m: $Memory T, s: $Memory T, a: int): $Memory T {
    $Memory(domain#$Memory(m)[a := domain#$Memory(s)[a]],
            contents#$Memory(m)[a := contents#$Memory(s)[a]])
}



// ============================================================================================
// Abort Handling

var $abort_flag: bool;
var $abort_code: int;

function {:inline} $process_abort_code(code: int): int {
    code
}

const $EXEC_FAILURE_CODE: int;
axiom $EXEC_FAILURE_CODE == -1;

// TODO(wrwg): currently we map aborts of native functions like those for vectors also to
//   execution failure. This may need to be aligned with what the runtime actually does.

procedure {:inline 1} $ExecFailureAbort() {
    $abort_flag := true;
    $abort_code := $EXEC_FAILURE_CODE;
}

procedure {:inline 1} $Abort(code: int) {
    $abort_flag := true;
    $abort_code := code;
}

function {:inline} $StdError(cat: int, reason: int): int {
    reason * 256 + cat
}

procedure {:inline 1} $InitVerification() {
    // Set abort_flag to false, and havoc abort_code
    $abort_flag := false;
    havoc $abort_code;
    // Initialize event store
    call $InitEventStore();
}

// ============================================================================================
// Instructions


procedure {:inline 1} $CastU8(src: int) returns (dst: int)
{
    if (src > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU16(src: int) returns (dst: int)
{
    if (src > $MAX_U16) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU32(src: int) returns (dst: int)
{
    if (src > $MAX_U32) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU64(src: int) returns (dst: int)
{
    if (src > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU128(src: int) returns (dst: int)
{
    if (src > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $CastU256(src: int) returns (dst: int)
{
    if (src > $MAX_U256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src;
}

procedure {:inline 1} $AddU8(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU16(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U16) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU16_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU32(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U32) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU32_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU64(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU64_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU128(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU128_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $AddU256(src1: int, src2: int) returns (dst: int)
{
    if (src1 + src2 > $MAX_U256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 + src2;
}

procedure {:inline 1} $AddU256_unchecked(src1: int, src2: int) returns (dst: int)
{
    dst := src1 + src2;
}

procedure {:inline 1} $Sub(src1: int, src2: int) returns (dst: int)
{
    if (src1 < src2) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 - src2;
}

// uninterpreted function to return an undefined value.
function $undefined_int(): int;

// Recursive exponentiation function
// Undefined unless e >=0.  $pow(0,0) is also undefined.
function $pow(n: int, e: int): int {
    if n != 0 && e == 0 then 1
    else if e > 0 then n * $pow(n, e - 1)
    else $undefined_int()
}

function $shl(src1: int, p: int): int {
    src1 * $pow(2, p)
}

function $shlU8(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 256
}

function $shlU16(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 65536
}

function $shlU32(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 4294967296
}

function $shlU64(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 18446744073709551616
}

function $shlU128(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 340282366920938463463374607431768211456
}

function $shlU256(src1: int, p: int): int {
    (src1 * $pow(2, p)) mod 115792089237316195423570985008687907853269984665640564039457584007913129639936
}

function $shr(src1: int, p: int): int {
    src1 div $pow(2, p)
}

// We need to know the size of the destination in order to drop bits
// that have been shifted left more than that, so we have $ShlU8/16/32/64/128/256
procedure {:inline 1} $ShlU8(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU8(src1, src2);
}

// Template for cast and shift operations of bitvector types

procedure {:inline 1} $CastBv8to8(src: bv8) returns (dst: bv8)
{
    dst := src;
}


function $shlBv8From8(src1: bv8, src2: bv8) returns (bv8)
{
    $Shl'Bv8'(src1, src2)
}

procedure {:inline 1} $ShlBv8From8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Ge'Bv8'(src2, 8bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2);
}

function $shrBv8From8(src1: bv8, src2: bv8) returns (bv8)
{
    $Shr'Bv8'(src1, src2)
}

procedure {:inline 1} $ShrBv8From8(src1: bv8, src2: bv8) returns (dst: bv8)
{
    if ($Ge'Bv8'(src2, 8bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2);
}

procedure {:inline 1} $CastBv16to8(src: bv16) returns (dst: bv8)
{
    if ($Gt'Bv16'(src, 255bv16)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From16(src1: bv8, src2: bv16) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From16(src1: bv8, src2: bv16) returns (dst: bv8)
{
    if ($Ge'Bv16'(src2, 8bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From16(src1: bv8, src2: bv16) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From16(src1: bv8, src2: bv16) returns (dst: bv8)
{
    if ($Ge'Bv16'(src2, 8bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv32to8(src: bv32) returns (dst: bv8)
{
    if ($Gt'Bv32'(src, 255bv32)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From32(src1: bv8, src2: bv32) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From32(src1: bv8, src2: bv32) returns (dst: bv8)
{
    if ($Ge'Bv32'(src2, 8bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From32(src1: bv8, src2: bv32) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From32(src1: bv8, src2: bv32) returns (dst: bv8)
{
    if ($Ge'Bv32'(src2, 8bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv64to8(src: bv64) returns (dst: bv8)
{
    if ($Gt'Bv64'(src, 255bv64)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From64(src1: bv8, src2: bv64) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From64(src1: bv8, src2: bv64) returns (dst: bv8)
{
    if ($Ge'Bv64'(src2, 8bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From64(src1: bv8, src2: bv64) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From64(src1: bv8, src2: bv64) returns (dst: bv8)
{
    if ($Ge'Bv64'(src2, 8bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv128to8(src: bv128) returns (dst: bv8)
{
    if ($Gt'Bv128'(src, 255bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From128(src1: bv8, src2: bv128) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From128(src1: bv8, src2: bv128) returns (dst: bv8)
{
    if ($Ge'Bv128'(src2, 8bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From128(src1: bv8, src2: bv128) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From128(src1: bv8, src2: bv128) returns (dst: bv8)
{
    if ($Ge'Bv128'(src2, 8bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv256to8(src: bv256) returns (dst: bv8)
{
    if ($Gt'Bv256'(src, 255bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[8:0];
}


function $shlBv8From256(src1: bv8, src2: bv256) returns (bv8)
{
    $Shl'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShlBv8From256(src1: bv8, src2: bv256) returns (dst: bv8)
{
    if ($Ge'Bv256'(src2, 8bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv8'(src1, src2[8:0]);
}

function $shrBv8From256(src1: bv8, src2: bv256) returns (bv8)
{
    $Shr'Bv8'(src1, src2[8:0])
}

procedure {:inline 1} $ShrBv8From256(src1: bv8, src2: bv256) returns (dst: bv8)
{
    if ($Ge'Bv256'(src2, 8bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv8'(src1, src2[8:0]);
}

procedure {:inline 1} $CastBv8to16(src: bv8) returns (dst: bv16)
{
    dst := 0bv8 ++ src;
}


function $shlBv16From8(src1: bv16, src2: bv8) returns (bv16)
{
    $Shl'Bv16'(src1, 0bv8 ++ src2)
}

procedure {:inline 1} $ShlBv16From8(src1: bv16, src2: bv8) returns (dst: bv16)
{
    if ($Ge'Bv8'(src2, 16bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, 0bv8 ++ src2);
}

function $shrBv16From8(src1: bv16, src2: bv8) returns (bv16)
{
    $Shr'Bv16'(src1, 0bv8 ++ src2)
}

procedure {:inline 1} $ShrBv16From8(src1: bv16, src2: bv8) returns (dst: bv16)
{
    if ($Ge'Bv8'(src2, 16bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, 0bv8 ++ src2);
}

procedure {:inline 1} $CastBv16to16(src: bv16) returns (dst: bv16)
{
    dst := src;
}


function $shlBv16From16(src1: bv16, src2: bv16) returns (bv16)
{
    $Shl'Bv16'(src1, src2)
}

procedure {:inline 1} $ShlBv16From16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Ge'Bv16'(src2, 16bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2);
}

function $shrBv16From16(src1: bv16, src2: bv16) returns (bv16)
{
    $Shr'Bv16'(src1, src2)
}

procedure {:inline 1} $ShrBv16From16(src1: bv16, src2: bv16) returns (dst: bv16)
{
    if ($Ge'Bv16'(src2, 16bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2);
}

procedure {:inline 1} $CastBv32to16(src: bv32) returns (dst: bv16)
{
    if ($Gt'Bv32'(src, 65535bv32)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From32(src1: bv16, src2: bv32) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From32(src1: bv16, src2: bv32) returns (dst: bv16)
{
    if ($Ge'Bv32'(src2, 16bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From32(src1: bv16, src2: bv32) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From32(src1: bv16, src2: bv32) returns (dst: bv16)
{
    if ($Ge'Bv32'(src2, 16bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv64to16(src: bv64) returns (dst: bv16)
{
    if ($Gt'Bv64'(src, 65535bv64)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From64(src1: bv16, src2: bv64) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From64(src1: bv16, src2: bv64) returns (dst: bv16)
{
    if ($Ge'Bv64'(src2, 16bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From64(src1: bv16, src2: bv64) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From64(src1: bv16, src2: bv64) returns (dst: bv16)
{
    if ($Ge'Bv64'(src2, 16bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv128to16(src: bv128) returns (dst: bv16)
{
    if ($Gt'Bv128'(src, 65535bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From128(src1: bv16, src2: bv128) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From128(src1: bv16, src2: bv128) returns (dst: bv16)
{
    if ($Ge'Bv128'(src2, 16bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From128(src1: bv16, src2: bv128) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From128(src1: bv16, src2: bv128) returns (dst: bv16)
{
    if ($Ge'Bv128'(src2, 16bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv256to16(src: bv256) returns (dst: bv16)
{
    if ($Gt'Bv256'(src, 65535bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[16:0];
}


function $shlBv16From256(src1: bv16, src2: bv256) returns (bv16)
{
    $Shl'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShlBv16From256(src1: bv16, src2: bv256) returns (dst: bv16)
{
    if ($Ge'Bv256'(src2, 16bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv16'(src1, src2[16:0]);
}

function $shrBv16From256(src1: bv16, src2: bv256) returns (bv16)
{
    $Shr'Bv16'(src1, src2[16:0])
}

procedure {:inline 1} $ShrBv16From256(src1: bv16, src2: bv256) returns (dst: bv16)
{
    if ($Ge'Bv256'(src2, 16bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv16'(src1, src2[16:0]);
}

procedure {:inline 1} $CastBv8to32(src: bv8) returns (dst: bv32)
{
    dst := 0bv24 ++ src;
}


function $shlBv32From8(src1: bv32, src2: bv8) returns (bv32)
{
    $Shl'Bv32'(src1, 0bv24 ++ src2)
}

procedure {:inline 1} $ShlBv32From8(src1: bv32, src2: bv8) returns (dst: bv32)
{
    if ($Ge'Bv8'(src2, 32bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, 0bv24 ++ src2);
}

function $shrBv32From8(src1: bv32, src2: bv8) returns (bv32)
{
    $Shr'Bv32'(src1, 0bv24 ++ src2)
}

procedure {:inline 1} $ShrBv32From8(src1: bv32, src2: bv8) returns (dst: bv32)
{
    if ($Ge'Bv8'(src2, 32bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, 0bv24 ++ src2);
}

procedure {:inline 1} $CastBv16to32(src: bv16) returns (dst: bv32)
{
    dst := 0bv16 ++ src;
}


function $shlBv32From16(src1: bv32, src2: bv16) returns (bv32)
{
    $Shl'Bv32'(src1, 0bv16 ++ src2)
}

procedure {:inline 1} $ShlBv32From16(src1: bv32, src2: bv16) returns (dst: bv32)
{
    if ($Ge'Bv16'(src2, 32bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, 0bv16 ++ src2);
}

function $shrBv32From16(src1: bv32, src2: bv16) returns (bv32)
{
    $Shr'Bv32'(src1, 0bv16 ++ src2)
}

procedure {:inline 1} $ShrBv32From16(src1: bv32, src2: bv16) returns (dst: bv32)
{
    if ($Ge'Bv16'(src2, 32bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, 0bv16 ++ src2);
}

procedure {:inline 1} $CastBv32to32(src: bv32) returns (dst: bv32)
{
    dst := src;
}


function $shlBv32From32(src1: bv32, src2: bv32) returns (bv32)
{
    $Shl'Bv32'(src1, src2)
}

procedure {:inline 1} $ShlBv32From32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Ge'Bv32'(src2, 32bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2);
}

function $shrBv32From32(src1: bv32, src2: bv32) returns (bv32)
{
    $Shr'Bv32'(src1, src2)
}

procedure {:inline 1} $ShrBv32From32(src1: bv32, src2: bv32) returns (dst: bv32)
{
    if ($Ge'Bv32'(src2, 32bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2);
}

procedure {:inline 1} $CastBv64to32(src: bv64) returns (dst: bv32)
{
    if ($Gt'Bv64'(src, 2147483647bv64)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[32:0];
}


function $shlBv32From64(src1: bv32, src2: bv64) returns (bv32)
{
    $Shl'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShlBv32From64(src1: bv32, src2: bv64) returns (dst: bv32)
{
    if ($Ge'Bv64'(src2, 32bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2[32:0]);
}

function $shrBv32From64(src1: bv32, src2: bv64) returns (bv32)
{
    $Shr'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShrBv32From64(src1: bv32, src2: bv64) returns (dst: bv32)
{
    if ($Ge'Bv64'(src2, 32bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2[32:0]);
}

procedure {:inline 1} $CastBv128to32(src: bv128) returns (dst: bv32)
{
    if ($Gt'Bv128'(src, 2147483647bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[32:0];
}


function $shlBv32From128(src1: bv32, src2: bv128) returns (bv32)
{
    $Shl'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShlBv32From128(src1: bv32, src2: bv128) returns (dst: bv32)
{
    if ($Ge'Bv128'(src2, 32bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2[32:0]);
}

function $shrBv32From128(src1: bv32, src2: bv128) returns (bv32)
{
    $Shr'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShrBv32From128(src1: bv32, src2: bv128) returns (dst: bv32)
{
    if ($Ge'Bv128'(src2, 32bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2[32:0]);
}

procedure {:inline 1} $CastBv256to32(src: bv256) returns (dst: bv32)
{
    if ($Gt'Bv256'(src, 2147483647bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[32:0];
}


function $shlBv32From256(src1: bv32, src2: bv256) returns (bv32)
{
    $Shl'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShlBv32From256(src1: bv32, src2: bv256) returns (dst: bv32)
{
    if ($Ge'Bv256'(src2, 32bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv32'(src1, src2[32:0]);
}

function $shrBv32From256(src1: bv32, src2: bv256) returns (bv32)
{
    $Shr'Bv32'(src1, src2[32:0])
}

procedure {:inline 1} $ShrBv32From256(src1: bv32, src2: bv256) returns (dst: bv32)
{
    if ($Ge'Bv256'(src2, 32bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv32'(src1, src2[32:0]);
}

procedure {:inline 1} $CastBv8to64(src: bv8) returns (dst: bv64)
{
    dst := 0bv56 ++ src;
}


function $shlBv64From8(src1: bv64, src2: bv8) returns (bv64)
{
    $Shl'Bv64'(src1, 0bv56 ++ src2)
}

procedure {:inline 1} $ShlBv64From8(src1: bv64, src2: bv8) returns (dst: bv64)
{
    if ($Ge'Bv8'(src2, 64bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, 0bv56 ++ src2);
}

function $shrBv64From8(src1: bv64, src2: bv8) returns (bv64)
{
    $Shr'Bv64'(src1, 0bv56 ++ src2)
}

procedure {:inline 1} $ShrBv64From8(src1: bv64, src2: bv8) returns (dst: bv64)
{
    if ($Ge'Bv8'(src2, 64bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, 0bv56 ++ src2);
}

procedure {:inline 1} $CastBv16to64(src: bv16) returns (dst: bv64)
{
    dst := 0bv48 ++ src;
}


function $shlBv64From16(src1: bv64, src2: bv16) returns (bv64)
{
    $Shl'Bv64'(src1, 0bv48 ++ src2)
}

procedure {:inline 1} $ShlBv64From16(src1: bv64, src2: bv16) returns (dst: bv64)
{
    if ($Ge'Bv16'(src2, 64bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, 0bv48 ++ src2);
}

function $shrBv64From16(src1: bv64, src2: bv16) returns (bv64)
{
    $Shr'Bv64'(src1, 0bv48 ++ src2)
}

procedure {:inline 1} $ShrBv64From16(src1: bv64, src2: bv16) returns (dst: bv64)
{
    if ($Ge'Bv16'(src2, 64bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, 0bv48 ++ src2);
}

procedure {:inline 1} $CastBv32to64(src: bv32) returns (dst: bv64)
{
    dst := 0bv32 ++ src;
}


function $shlBv64From32(src1: bv64, src2: bv32) returns (bv64)
{
    $Shl'Bv64'(src1, 0bv32 ++ src2)
}

procedure {:inline 1} $ShlBv64From32(src1: bv64, src2: bv32) returns (dst: bv64)
{
    if ($Ge'Bv32'(src2, 64bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, 0bv32 ++ src2);
}

function $shrBv64From32(src1: bv64, src2: bv32) returns (bv64)
{
    $Shr'Bv64'(src1, 0bv32 ++ src2)
}

procedure {:inline 1} $ShrBv64From32(src1: bv64, src2: bv32) returns (dst: bv64)
{
    if ($Ge'Bv32'(src2, 64bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, 0bv32 ++ src2);
}

procedure {:inline 1} $CastBv64to64(src: bv64) returns (dst: bv64)
{
    dst := src;
}


function $shlBv64From64(src1: bv64, src2: bv64) returns (bv64)
{
    $Shl'Bv64'(src1, src2)
}

procedure {:inline 1} $ShlBv64From64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Ge'Bv64'(src2, 64bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, src2);
}

function $shrBv64From64(src1: bv64, src2: bv64) returns (bv64)
{
    $Shr'Bv64'(src1, src2)
}

procedure {:inline 1} $ShrBv64From64(src1: bv64, src2: bv64) returns (dst: bv64)
{
    if ($Ge'Bv64'(src2, 64bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, src2);
}

procedure {:inline 1} $CastBv128to64(src: bv128) returns (dst: bv64)
{
    if ($Gt'Bv128'(src, 18446744073709551615bv128)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[64:0];
}


function $shlBv64From128(src1: bv64, src2: bv128) returns (bv64)
{
    $Shl'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShlBv64From128(src1: bv64, src2: bv128) returns (dst: bv64)
{
    if ($Ge'Bv128'(src2, 64bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, src2[64:0]);
}

function $shrBv64From128(src1: bv64, src2: bv128) returns (bv64)
{
    $Shr'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShrBv64From128(src1: bv64, src2: bv128) returns (dst: bv64)
{
    if ($Ge'Bv128'(src2, 64bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, src2[64:0]);
}

procedure {:inline 1} $CastBv256to64(src: bv256) returns (dst: bv64)
{
    if ($Gt'Bv256'(src, 18446744073709551615bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[64:0];
}


function $shlBv64From256(src1: bv64, src2: bv256) returns (bv64)
{
    $Shl'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShlBv64From256(src1: bv64, src2: bv256) returns (dst: bv64)
{
    if ($Ge'Bv256'(src2, 64bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv64'(src1, src2[64:0]);
}

function $shrBv64From256(src1: bv64, src2: bv256) returns (bv64)
{
    $Shr'Bv64'(src1, src2[64:0])
}

procedure {:inline 1} $ShrBv64From256(src1: bv64, src2: bv256) returns (dst: bv64)
{
    if ($Ge'Bv256'(src2, 64bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv64'(src1, src2[64:0]);
}

procedure {:inline 1} $CastBv8to128(src: bv8) returns (dst: bv128)
{
    dst := 0bv120 ++ src;
}


function $shlBv128From8(src1: bv128, src2: bv8) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv120 ++ src2)
}

procedure {:inline 1} $ShlBv128From8(src1: bv128, src2: bv8) returns (dst: bv128)
{
    if ($Ge'Bv8'(src2, 128bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv120 ++ src2);
}

function $shrBv128From8(src1: bv128, src2: bv8) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv120 ++ src2)
}

procedure {:inline 1} $ShrBv128From8(src1: bv128, src2: bv8) returns (dst: bv128)
{
    if ($Ge'Bv8'(src2, 128bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv120 ++ src2);
}

procedure {:inline 1} $CastBv16to128(src: bv16) returns (dst: bv128)
{
    dst := 0bv112 ++ src;
}


function $shlBv128From16(src1: bv128, src2: bv16) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv112 ++ src2)
}

procedure {:inline 1} $ShlBv128From16(src1: bv128, src2: bv16) returns (dst: bv128)
{
    if ($Ge'Bv16'(src2, 128bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv112 ++ src2);
}

function $shrBv128From16(src1: bv128, src2: bv16) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv112 ++ src2)
}

procedure {:inline 1} $ShrBv128From16(src1: bv128, src2: bv16) returns (dst: bv128)
{
    if ($Ge'Bv16'(src2, 128bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv112 ++ src2);
}

procedure {:inline 1} $CastBv32to128(src: bv32) returns (dst: bv128)
{
    dst := 0bv96 ++ src;
}


function $shlBv128From32(src1: bv128, src2: bv32) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv96 ++ src2)
}

procedure {:inline 1} $ShlBv128From32(src1: bv128, src2: bv32) returns (dst: bv128)
{
    if ($Ge'Bv32'(src2, 128bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv96 ++ src2);
}

function $shrBv128From32(src1: bv128, src2: bv32) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv96 ++ src2)
}

procedure {:inline 1} $ShrBv128From32(src1: bv128, src2: bv32) returns (dst: bv128)
{
    if ($Ge'Bv32'(src2, 128bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv96 ++ src2);
}

procedure {:inline 1} $CastBv64to128(src: bv64) returns (dst: bv128)
{
    dst := 0bv64 ++ src;
}


function $shlBv128From64(src1: bv128, src2: bv64) returns (bv128)
{
    $Shl'Bv128'(src1, 0bv64 ++ src2)
}

procedure {:inline 1} $ShlBv128From64(src1: bv128, src2: bv64) returns (dst: bv128)
{
    if ($Ge'Bv64'(src2, 128bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, 0bv64 ++ src2);
}

function $shrBv128From64(src1: bv128, src2: bv64) returns (bv128)
{
    $Shr'Bv128'(src1, 0bv64 ++ src2)
}

procedure {:inline 1} $ShrBv128From64(src1: bv128, src2: bv64) returns (dst: bv128)
{
    if ($Ge'Bv64'(src2, 128bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, 0bv64 ++ src2);
}

procedure {:inline 1} $CastBv128to128(src: bv128) returns (dst: bv128)
{
    dst := src;
}


function $shlBv128From128(src1: bv128, src2: bv128) returns (bv128)
{
    $Shl'Bv128'(src1, src2)
}

procedure {:inline 1} $ShlBv128From128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Ge'Bv128'(src2, 128bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, src2);
}

function $shrBv128From128(src1: bv128, src2: bv128) returns (bv128)
{
    $Shr'Bv128'(src1, src2)
}

procedure {:inline 1} $ShrBv128From128(src1: bv128, src2: bv128) returns (dst: bv128)
{
    if ($Ge'Bv128'(src2, 128bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, src2);
}

procedure {:inline 1} $CastBv256to128(src: bv256) returns (dst: bv128)
{
    if ($Gt'Bv256'(src, 340282366920938463463374607431768211455bv256)) {
            call $ExecFailureAbort();
            return;
    }
    dst := src[128:0];
}


function $shlBv128From256(src1: bv128, src2: bv256) returns (bv128)
{
    $Shl'Bv128'(src1, src2[128:0])
}

procedure {:inline 1} $ShlBv128From256(src1: bv128, src2: bv256) returns (dst: bv128)
{
    if ($Ge'Bv256'(src2, 128bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv128'(src1, src2[128:0]);
}

function $shrBv128From256(src1: bv128, src2: bv256) returns (bv128)
{
    $Shr'Bv128'(src1, src2[128:0])
}

procedure {:inline 1} $ShrBv128From256(src1: bv128, src2: bv256) returns (dst: bv128)
{
    if ($Ge'Bv256'(src2, 128bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv128'(src1, src2[128:0]);
}

procedure {:inline 1} $CastBv8to256(src: bv8) returns (dst: bv256)
{
    dst := 0bv248 ++ src;
}


function $shlBv256From8(src1: bv256, src2: bv8) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv248 ++ src2)
}

procedure {:inline 1} $ShlBv256From8(src1: bv256, src2: bv8) returns (dst: bv256)
{
    if ($Ge'Bv8'(src2, 256bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv248 ++ src2);
}

function $shrBv256From8(src1: bv256, src2: bv8) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv248 ++ src2)
}

procedure {:inline 1} $ShrBv256From8(src1: bv256, src2: bv8) returns (dst: bv256)
{
    if ($Ge'Bv8'(src2, 256bv8)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv248 ++ src2);
}

procedure {:inline 1} $CastBv16to256(src: bv16) returns (dst: bv256)
{
    dst := 0bv240 ++ src;
}


function $shlBv256From16(src1: bv256, src2: bv16) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv240 ++ src2)
}

procedure {:inline 1} $ShlBv256From16(src1: bv256, src2: bv16) returns (dst: bv256)
{
    if ($Ge'Bv16'(src2, 256bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv240 ++ src2);
}

function $shrBv256From16(src1: bv256, src2: bv16) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv240 ++ src2)
}

procedure {:inline 1} $ShrBv256From16(src1: bv256, src2: bv16) returns (dst: bv256)
{
    if ($Ge'Bv16'(src2, 256bv16)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv240 ++ src2);
}

procedure {:inline 1} $CastBv32to256(src: bv32) returns (dst: bv256)
{
    dst := 0bv224 ++ src;
}


function $shlBv256From32(src1: bv256, src2: bv32) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv224 ++ src2)
}

procedure {:inline 1} $ShlBv256From32(src1: bv256, src2: bv32) returns (dst: bv256)
{
    if ($Ge'Bv32'(src2, 256bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv224 ++ src2);
}

function $shrBv256From32(src1: bv256, src2: bv32) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv224 ++ src2)
}

procedure {:inline 1} $ShrBv256From32(src1: bv256, src2: bv32) returns (dst: bv256)
{
    if ($Ge'Bv32'(src2, 256bv32)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv224 ++ src2);
}

procedure {:inline 1} $CastBv64to256(src: bv64) returns (dst: bv256)
{
    dst := 0bv192 ++ src;
}


function $shlBv256From64(src1: bv256, src2: bv64) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv192 ++ src2)
}

procedure {:inline 1} $ShlBv256From64(src1: bv256, src2: bv64) returns (dst: bv256)
{
    if ($Ge'Bv64'(src2, 256bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv192 ++ src2);
}

function $shrBv256From64(src1: bv256, src2: bv64) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv192 ++ src2)
}

procedure {:inline 1} $ShrBv256From64(src1: bv256, src2: bv64) returns (dst: bv256)
{
    if ($Ge'Bv64'(src2, 256bv64)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv192 ++ src2);
}

procedure {:inline 1} $CastBv128to256(src: bv128) returns (dst: bv256)
{
    dst := 0bv128 ++ src;
}


function $shlBv256From128(src1: bv256, src2: bv128) returns (bv256)
{
    $Shl'Bv256'(src1, 0bv128 ++ src2)
}

procedure {:inline 1} $ShlBv256From128(src1: bv256, src2: bv128) returns (dst: bv256)
{
    if ($Ge'Bv128'(src2, 256bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, 0bv128 ++ src2);
}

function $shrBv256From128(src1: bv256, src2: bv128) returns (bv256)
{
    $Shr'Bv256'(src1, 0bv128 ++ src2)
}

procedure {:inline 1} $ShrBv256From128(src1: bv256, src2: bv128) returns (dst: bv256)
{
    if ($Ge'Bv128'(src2, 256bv128)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, 0bv128 ++ src2);
}

procedure {:inline 1} $CastBv256to256(src: bv256) returns (dst: bv256)
{
    dst := src;
}


function $shlBv256From256(src1: bv256, src2: bv256) returns (bv256)
{
    $Shl'Bv256'(src1, src2)
}

procedure {:inline 1} $ShlBv256From256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Ge'Bv256'(src2, 256bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shl'Bv256'(src1, src2);
}

function $shrBv256From256(src1: bv256, src2: bv256) returns (bv256)
{
    $Shr'Bv256'(src1, src2)
}

procedure {:inline 1} $ShrBv256From256(src1: bv256, src2: bv256) returns (dst: bv256)
{
    if ($Ge'Bv256'(src2, 256bv256)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Shr'Bv256'(src1, src2);
}

procedure {:inline 1} $ShlU16(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU16(src1, src2);
}

procedure {:inline 1} $ShlU32(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU32(src1, src2);
}

procedure {:inline 1} $ShlU64(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 64) {
       call $ExecFailureAbort();
       return;
    }
    dst := $shlU64(src1, src2);
}

procedure {:inline 1} $ShlU128(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shlU128(src1, src2);
}

procedure {:inline 1} $ShlU256(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shlU256(src1, src2);
}

procedure {:inline 1} $Shr(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU8(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 8) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU16(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 16) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU32(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 32) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU64(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 64) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU128(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    if (src2 >= 128) {
        call $ExecFailureAbort();
        return;
    }
    dst := $shr(src1, src2);
}

procedure {:inline 1} $ShrU256(src1: int, src2: int) returns (dst: int)
{
    var res: int;
    // src2 is a u8
    assume src2 >= 0 && src2 < 256;
    dst := $shr(src1, src2);
}

procedure {:inline 1} $MulU8(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U8) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU16(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U16) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU32(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U32) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU64(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U64) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU128(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U128) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $MulU256(src1: int, src2: int) returns (dst: int)
{
    if (src1 * src2 > $MAX_U256) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 * src2;
}

procedure {:inline 1} $Div(src1: int, src2: int) returns (dst: int)
{
    if (src2 == 0) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 div src2;
}

procedure {:inline 1} $Mod(src1: int, src2: int) returns (dst: int)
{
    if (src2 == 0) {
        call $ExecFailureAbort();
        return;
    }
    dst := src1 mod src2;
}

procedure {:inline 1} $ArithBinaryUnimplemented(src1: int, src2: int) returns (dst: int);

procedure {:inline 1} $Lt(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 < src2;
}

procedure {:inline 1} $Gt(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 > src2;
}

procedure {:inline 1} $Le(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 <= src2;
}

procedure {:inline 1} $Ge(src1: int, src2: int) returns (dst: bool)
{
    dst := src1 >= src2;
}

procedure {:inline 1} $And(src1: bool, src2: bool) returns (dst: bool)
{
    dst := src1 && src2;
}

procedure {:inline 1} $Or(src1: bool, src2: bool) returns (dst: bool)
{
    dst := src1 || src2;
}

procedure {:inline 1} $Not(src: bool) returns (dst: bool)
{
    dst := !src;
}

// Pack and Unpack are auto-generated for each type T


// ==================================================================================
// Native Vector

function {:inline} $SliceVecByRange<T>(v: Vec T, r: $Range): Vec T {
    SliceVec(v, lb#$Range(r), ub#$Range(r))
}

// ----------------------------------------------------------------------------------
// Native Vector implementation for element type `u8`

// Not inlined. It appears faster this way.
function $IsEqual'vec'u8''(v1: Vec (int), v2: Vec (int)): bool {
    LenVec(v1) == LenVec(v2) &&
    (forall i: int:: InRangeVec(v1, i) ==> $IsEqual'u8'(ReadVec(v1, i), ReadVec(v2, i)))
}

// Not inlined.
function $IsPrefix'vec'u8''(v: Vec (int), prefix: Vec (int)): bool {
    LenVec(v) >= LenVec(prefix) &&
    (forall i: int:: InRangeVec(prefix, i) ==> $IsEqual'u8'(ReadVec(v, i), ReadVec(prefix, i)))
}

// Not inlined.
function $IsSuffix'vec'u8''(v: Vec (int), suffix: Vec (int)): bool {
    LenVec(v) >= LenVec(suffix) &&
    (forall i: int:: InRangeVec(suffix, i) ==> $IsEqual'u8'(ReadVec(v, LenVec(v) - LenVec(suffix) + i), ReadVec(suffix, i)))
}

// Not inlined.
function $IsValid'vec'u8''(v: Vec (int)): bool {
    $IsValid'u64'(LenVec(v)) &&
    (forall i: int:: InRangeVec(v, i) ==> $IsValid'u8'(ReadVec(v, i)))
}


function {:inline} $ContainsVec'u8'(v: Vec (int), e: int): bool {
    (exists i: int :: $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u8'(ReadVec(v, i), e))
}

function $IndexOfVec'u8'(v: Vec (int), e: int): int;
axiom (forall v: Vec (int), e: int:: {$IndexOfVec'u8'(v, e)}
    (var i := $IndexOfVec'u8'(v, e);
     if (!$ContainsVec'u8'(v, e)) then i == -1
     else $IsValid'u64'(i) && InRangeVec(v, i) && $IsEqual'u8'(ReadVec(v, i), e) &&
        (forall j: int :: $IsValid'u64'(j) && j >= 0 && j < i ==> !$IsEqual'u8'(ReadVec(v, j), e))));


function {:inline} $RangeVec'u8'(v: Vec (int)): $Range {
    $Range(0, LenVec(v))
}


function {:inline} $EmptyVec'u8'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_empty'u8'() returns (v: Vec (int)) {
    v := EmptyVec();
}

function {:inline} $1_vector_$empty'u8'(): Vec (int) {
    EmptyVec()
}

procedure {:inline 1} $1_vector_is_empty'u8'(v: Vec (int)) returns (b: bool) {
    b := IsEmptyVec(v);
}

procedure {:inline 1} $1_vector_push_back'u8'(m: $Mutation (Vec (int)), val: int) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ExtendVec($Dereference(m), val));
}

function {:inline} $1_vector_$push_back'u8'(v: Vec (int), val: int): Vec (int) {
    ExtendVec(v, val)
}

procedure {:inline 1} $1_vector_pop_back'u8'(m: $Mutation (Vec (int))) returns (e: int, m': $Mutation (Vec (int))) {
    var v: Vec (int);
    var len: int;
    v := $Dereference(m);
    len := LenVec(v);
    if (len == 0) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, len-1);
    m' := $UpdateMutation(m, RemoveVec(v));
}

procedure {:inline 1} $1_vector_append'u8'(m: $Mutation (Vec (int)), other: Vec (int)) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ConcatVec($Dereference(m), other));
}

procedure {:inline 1} $1_vector_reverse'u8'(m: $Mutation (Vec (int))) returns (m': $Mutation (Vec (int))) {
    m' := $UpdateMutation(m, ReverseVec($Dereference(m)));
}

procedure {:inline 1} $1_vector_length'u8'(v: Vec (int)) returns (l: int) {
    l := LenVec(v);
}

function {:inline} $1_vector_$length'u8'(v: Vec (int)): int {
    LenVec(v)
}

procedure {:inline 1} $1_vector_borrow'u8'(v: Vec (int), i: int) returns (dst: int) {
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    dst := ReadVec(v, i);
}

function {:inline} $1_vector_$borrow'u8'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_borrow_mut'u8'(m: $Mutation (Vec (int)), index: int)
returns (dst: $Mutation (int), m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, index)) {
        call $ExecFailureAbort();
        return;
    }
    dst := $Mutation(l#$Mutation(m), ExtendVec(p#$Mutation(m), index), ReadVec(v, index));
    m' := m;
}

function {:inline} $1_vector_$borrow_mut'u8'(v: Vec (int), i: int): int {
    ReadVec(v, i)
}

procedure {:inline 1} $1_vector_destroy_empty'u8'(v: Vec (int)) {
    if (!IsEmptyVec(v)) {
      call $ExecFailureAbort();
    }
}

procedure {:inline 1} $1_vector_swap'u8'(m: $Mutation (Vec (int)), i: int, j: int) returns (m': $Mutation (Vec (int)))
{
    var v: Vec (int);
    v := $Dereference(m);
    if (!InRangeVec(v, i) || !InRangeVec(v, j)) {
        call $ExecFailureAbort();
        return;
    }
    m' := $UpdateMutation(m, SwapVec(v, i, j));
}

function {:inline} $1_vector_$swap'u8'(v: Vec (int), i: int, j: int): Vec (int) {
    SwapVec(v, i, j)
}

procedure {:inline 1} $1_vector_remove'u8'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var v: Vec (int);

    v := $Dereference(m);

    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveAtVec(v, i));
}

procedure {:inline 1} $1_vector_insert'u8'(m: $Mutation (Vec (int)), val: int, i: int) returns (m': $Mutation (Vec (int))) {

    var len: int;
    var v: Vec (int);

    v := $Dereference(m);

    len := LenVec(v);
    if (i < 0 || i > len) {
        call $ExecFailureAbort();
        return;
    }
    if (i == len) {
        m' := $UpdateMutation(m, ExtendVec(v, val));
    } else {
        m' := $UpdateMutation(m, InsertAtVec(v, i, val));
    }
}

procedure {:inline 1} $1_vector_swap_remove'u8'(m: $Mutation (Vec (int)), i: int) returns (e: int, m': $Mutation (Vec (int)))
{
    var len: int;
    var v: Vec (int);

    v := $Dereference(m);
    len := LenVec(v);
    if (!InRangeVec(v, i)) {
        call $ExecFailureAbort();
        return;
    }
    e := ReadVec(v, i);
    m' := $UpdateMutation(m, RemoveVec(SwapVec(v, i, len-1)));
}

procedure {:inline 1} $1_vector_contains'u8'(v: Vec (int), e: int) returns (res: bool)  {
    res := $ContainsVec'u8'(v, e);
}

procedure {:inline 1}
$1_vector_index_of'u8'(v: Vec (int), e: int) returns (res1: bool, res2: int) {
    res2 := $IndexOfVec'u8'(v, e);
    if (res2 >= 0) {
        res1 := true;
    } else {
        res1 := false;
        res2 := 0;
    }
}


// ==================================================================================
// Native Table

// ==================================================================================
// Native Hash

// Hash is modeled as an otherwise uninterpreted injection.
// In truth, it is not an injection since the domain has greater cardinality
// (arbitrary length vectors) than the co-domain (vectors of length 32).  But it is
// common to assume in code there are no hash collisions in practice.  Fortunately,
// Boogie is not smart enough to recognized that there is an inconsistency.
// FIXME: If we were using a reliable extensional theory of arrays, and if we could use ==
// instead of $IsEqual, we might be able to avoid so many quantified formulas by
// using a sha2_inverse function in the ensures conditions of Hash_sha2_256 to
// assert that sha2/3 are injections without using global quantified axioms.


function $1_hash_sha2(val: Vec int): Vec int;

// This says that Hash_sha2 is bijective.
axiom (forall v1,v2: Vec int :: {$1_hash_sha2(v1), $1_hash_sha2(v2)}
       $IsEqual'vec'u8''(v1, v2) <==> $IsEqual'vec'u8''($1_hash_sha2(v1), $1_hash_sha2(v2)));

procedure $1_hash_sha2_256(val: Vec int) returns (res: Vec int);
ensures res == $1_hash_sha2(val);     // returns Hash_sha2 Value
ensures $IsValid'vec'u8''(res);    // result is a legal vector of U8s.
ensures LenVec(res) == 32;               // result is 32 bytes.

// Spec version of Move native function.
function {:inline} $1_hash_$sha2_256(val: Vec int): Vec int {
    $1_hash_sha2(val)
}

// similarly for Hash_sha3
function $1_hash_sha3(val: Vec int): Vec int;

axiom (forall v1,v2: Vec int :: {$1_hash_sha3(v1), $1_hash_sha3(v2)}
       $IsEqual'vec'u8''(v1, v2) <==> $IsEqual'vec'u8''($1_hash_sha3(v1), $1_hash_sha3(v2)));

procedure $1_hash_sha3_256(val: Vec int) returns (res: Vec int);
ensures res == $1_hash_sha3(val);     // returns Hash_sha3 Value
ensures $IsValid'vec'u8''(res);    // result is a legal vector of U8s.
ensures LenVec(res) == 32;               // result is 32 bytes.

// Spec version of Move native function.
function {:inline} $1_hash_$sha3_256(val: Vec int): Vec int {
    $1_hash_sha3(val)
}

// ==================================================================================
// Native string

// TODO: correct implementation of strings

procedure {:inline 1} $1_string_internal_check_utf8(x: Vec int) returns (r: bool) {
}

procedure {:inline 1} $1_string_internal_sub_string(x: Vec int, i: int, j: int) returns (r: Vec int) {
}

procedure {:inline 1} $1_string_internal_index_of(x: Vec int, y: Vec int) returns (r: int) {
}

procedure {:inline 1} $1_string_internal_is_char_boundary(x: Vec int, i: int) returns (r: bool) {
}




// ==================================================================================
// Native diem_account

procedure {:inline 1} $1_DiemAccount_create_signer(
  addr: int
) returns (signer: $signer) {
    // A signer is currently identical to an address.
    signer := $signer(addr);
}

procedure {:inline 1} $1_DiemAccount_destroy_signer(
  signer: $signer
) {
  return;
}

// ==================================================================================
// Native account

procedure {:inline 1} $1_Account_create_signer(
  addr: int
) returns (signer: $signer) {
    // A signer is currently identical to an address.
    signer := $signer(addr);
}

// ==================================================================================
// Native Signer

type {:datatype} $signer;
function {:constructor} $signer($addr: int): $signer;
function {:inline} $IsValid'signer'(s: $signer): bool {
    $IsValid'address'($addr#$signer(s))
}
function {:inline} $IsEqual'signer'(s1: $signer, s2: $signer): bool {
    s1 == s2
}

procedure {:inline 1} $1_signer_borrow_address(signer: $signer) returns (res: int) {
    res := $addr#$signer(signer);
}

function {:inline} $1_signer_$borrow_address(signer: $signer): int
{
    $addr#$signer(signer)
}

function $1_signer_is_txn_signer(s: $signer): bool;

function $1_signer_is_txn_signer_addr(a: int): bool;


// ==================================================================================
// Native signature

// Signature related functionality is handled via uninterpreted functions. This is sound
// currently because we verify every code path based on signature verification with
// an arbitrary interpretation.

function $1_Signature_$ed25519_validate_pubkey(public_key: Vec int): bool;
function $1_Signature_$ed25519_verify(signature: Vec int, public_key: Vec int, message: Vec int): bool;

// Needed because we do not have extensional equality:
axiom (forall k1, k2: Vec int ::
    {$1_Signature_$ed25519_validate_pubkey(k1), $1_Signature_$ed25519_validate_pubkey(k2)}
    $IsEqual'vec'u8''(k1, k2) ==> $1_Signature_$ed25519_validate_pubkey(k1) == $1_Signature_$ed25519_validate_pubkey(k2));
axiom (forall s1, s2, k1, k2, m1, m2: Vec int ::
    {$1_Signature_$ed25519_verify(s1, k1, m1), $1_Signature_$ed25519_verify(s2, k2, m2)}
    $IsEqual'vec'u8''(s1, s2) && $IsEqual'vec'u8''(k1, k2) && $IsEqual'vec'u8''(m1, m2)
    ==> $1_Signature_$ed25519_verify(s1, k1, m1) == $1_Signature_$ed25519_verify(s2, k2, m2));


procedure {:inline 1} $1_Signature_ed25519_validate_pubkey(public_key: Vec int) returns (res: bool) {
    res := $1_Signature_$ed25519_validate_pubkey(public_key);
}

procedure {:inline 1} $1_Signature_ed25519_verify(
        signature: Vec int, public_key: Vec int, message: Vec int) returns (res: bool) {
    res := $1_Signature_$ed25519_verify(signature, public_key, message);
}


// ==================================================================================
// Native bcs::serialize


// ==================================================================================
// Native Event module



procedure {:inline 1} $InitEventStore() {
}

// ============================================================================================
// Type Reflection on Type Parameters

type {:datatype} $TypeParamInfo;

function {:constructor} $TypeParamBool(): $TypeParamInfo;
function {:constructor} $TypeParamU8(): $TypeParamInfo;
function {:constructor} $TypeParamU16(): $TypeParamInfo;
function {:constructor} $TypeParamU32(): $TypeParamInfo;
function {:constructor} $TypeParamU64(): $TypeParamInfo;
function {:constructor} $TypeParamU128(): $TypeParamInfo;
function {:constructor} $TypeParamU256(): $TypeParamInfo;
function {:constructor} $TypeParamAddress(): $TypeParamInfo;
function {:constructor} $TypeParamSigner(): $TypeParamInfo;
function {:constructor} $TypeParamVector(e: $TypeParamInfo): $TypeParamInfo;
function {:constructor} $TypeParamStruct(a: int, m: Vec int, s: Vec int): $TypeParamInfo;



//==================================
// Begin Translation

function $TypeName(t: $TypeParamInfo): Vec int;
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamBool(t) ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 98][1 := 111][2 := 111][3 := 108], 4)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 98][1 := 111][2 := 111][3 := 108], 4)) ==> is#$TypeParamBool(t));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamU8(t) ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 56], 2)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 56], 2)) ==> is#$TypeParamU8(t));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamU16(t) ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 54], 3)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 54], 3)) ==> is#$TypeParamU16(t));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamU32(t) ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 51][2 := 50], 3)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 51][2 := 50], 3)) ==> is#$TypeParamU32(t));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamU64(t) ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 54][2 := 52], 3)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 54][2 := 52], 3)) ==> is#$TypeParamU64(t));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamU128(t) ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 50][3 := 56], 4)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 49][2 := 50][3 := 56], 4)) ==> is#$TypeParamU128(t));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamU256(t) ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 50][2 := 53][3 := 54], 4)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 117][1 := 50][2 := 53][3 := 54], 4)) ==> is#$TypeParamU256(t));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamAddress(t) ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 97][1 := 100][2 := 100][3 := 114][4 := 101][5 := 115][6 := 115], 7)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 97][1 := 100][2 := 100][3 := 114][4 := 101][5 := 115][6 := 115], 7)) ==> is#$TypeParamAddress(t));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamSigner(t) ==> $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 115][1 := 105][2 := 103][3 := 110][4 := 101][5 := 114], 6)));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsEqual'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 115][1 := 105][2 := 103][3 := 110][4 := 101][5 := 114], 6)) ==> is#$TypeParamSigner(t));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamVector(t) ==> $IsEqual'vec'u8''($TypeName(t), ConcatVec(ConcatVec(Vec(DefaultVecMap()[0 := 118][1 := 101][2 := 99][3 := 116][4 := 111][5 := 114][6 := 60], 7), $TypeName(e#$TypeParamVector(t))), Vec(DefaultVecMap()[0 := 62], 1))));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} ($IsPrefix'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 118][1 := 101][2 := 99][3 := 116][4 := 111][5 := 114][6 := 60], 7)) && $IsSuffix'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 62], 1))) ==> is#$TypeParamVector(t));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} is#$TypeParamStruct(t) ==> $IsEqual'vec'u8''($TypeName(t), ConcatVec(ConcatVec(ConcatVec(ConcatVec(ConcatVec(Vec(DefaultVecMap()[0 := 48][1 := 120], 2), MakeVec1(a#$TypeParamStruct(t))), Vec(DefaultVecMap()[0 := 58][1 := 58], 2)), m#$TypeParamStruct(t)), Vec(DefaultVecMap()[0 := 58][1 := 58], 2)), s#$TypeParamStruct(t))));
axiom (forall t: $TypeParamInfo :: {$TypeName(t)} $IsPrefix'vec'u8''($TypeName(t), Vec(DefaultVecMap()[0 := 48][1 := 120], 2)) ==> is#$TypeParamVector(t));


// Given Types for Type Parameters

type #0;
function {:inline} $IsEqual'#0'(x1: #0, x2: #0): bool { x1 == x2 }
function {:inline} $IsValid'#0'(x: #0): bool { true }
var #0_info: $TypeParamInfo;

// fun signer::address_of [baseline] at C:\Users\baps/.move\https___github_com_move-language_move_git_main\language/move-stdlib\sources\signer.move:12:5+79
procedure {:inline 1} $1_signer_address_of(_$t0: $signer) returns ($ret0: int)
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t0: $signer;
    var $temp_0'address': int;
    var $temp_0'signer': $signer;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[s]($t0) at C:\Users\baps/.move\https___github_com_move-language_move_git_main\language/move-stdlib\sources\signer.move:12:5+1
    assume {:print "$at(11,400,401)"} true;
    assume {:print "$track_local(0,0,0):", $t0} $t0 == $t0;

    // $t1 := signer::borrow_address($t0) on_abort goto L2 with $t2 at C:\Users\baps/.move\https___github_com_move-language_move_git_main\language/move-stdlib\sources\signer.move:13:10+17
    assume {:print "$at(11,455,472)"} true;
    call $t1 := $1_signer_borrow_address($t0);
    if ($abort_flag) {
        assume {:print "$at(11,455,472)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(0,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // trace_return[0]($t1) at C:\Users\baps/.move\https___github_com_move-language_move_git_main\language/move-stdlib\sources\signer.move:13:9+18
    assume {:print "$track_return(0,0,0):", $t1} $t1 == $t1;

    // label L1 at C:\Users\baps/.move\https___github_com_move-language_move_git_main\language/move-stdlib\sources\signer.move:14:5+1
    assume {:print "$at(11,478,479)"} true;
L1:

    // return $t1 at C:\Users\baps/.move\https___github_com_move-language_move_git_main\language/move-stdlib\sources\signer.move:14:5+1
    assume {:print "$at(11,478,479)"} true;
    $ret0 := $t1;
    return;

    // label L2 at C:\Users\baps/.move\https___github_com_move-language_move_git_main\language/move-stdlib\sources\signer.move:14:5+1
L2:

    // abort($t2) at C:\Users\baps/.move\https___github_com_move-language_move_git_main\language/move-stdlib\sources\signer.move:14:5+1
    assume {:print "$at(11,478,479)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// struct BasicCoin::Balance<MyOddCoin::MyOddCoin> at .\sources\FirstModule.move:14:5+79
type {:datatype} $cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin';
function {:constructor} $cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin'($coin: $cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin'): $cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin';
function {:inline} $Update'$cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin''_coin(s: $cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin', x: $cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin'): $cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin' {
    $cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin'(x)
}
function $IsValid'$cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin''(s: $cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin'): bool {
    $IsValid'$cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin''($coin#$cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin'(s))
}
function {:inline} $IsEqual'$cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin''(s1: $cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin', s2: $cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin'): bool {
    s1 == s2
}
var $cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin'_$memory: $Memory $cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin';

// struct BasicCoin::Balance<#0> at .\sources\FirstModule.move:14:5+79
type {:datatype} $cafe_BasicCoin_Balance'#0';
function {:constructor} $cafe_BasicCoin_Balance'#0'($coin: $cafe_BasicCoin_Coin'#0'): $cafe_BasicCoin_Balance'#0';
function {:inline} $Update'$cafe_BasicCoin_Balance'#0''_coin(s: $cafe_BasicCoin_Balance'#0', x: $cafe_BasicCoin_Coin'#0'): $cafe_BasicCoin_Balance'#0' {
    $cafe_BasicCoin_Balance'#0'(x)
}
function $IsValid'$cafe_BasicCoin_Balance'#0''(s: $cafe_BasicCoin_Balance'#0'): bool {
    $IsValid'$cafe_BasicCoin_Coin'#0''($coin#$cafe_BasicCoin_Balance'#0'(s))
}
function {:inline} $IsEqual'$cafe_BasicCoin_Balance'#0''(s1: $cafe_BasicCoin_Balance'#0', s2: $cafe_BasicCoin_Balance'#0'): bool {
    s1 == s2
}
var $cafe_BasicCoin_Balance'#0'_$memory: $Memory $cafe_BasicCoin_Balance'#0';

// struct BasicCoin::Coin<MyOddCoin::MyOddCoin> at .\sources\FirstModule.move:10:5+69
type {:datatype} $cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin';
function {:constructor} $cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin'($value: int): $cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin';
function {:inline} $Update'$cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin''_value(s: $cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin', x: int): $cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin' {
    $cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin'(x)
}
function $IsValid'$cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin''(s: $cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin'): bool {
    $IsValid'u64'($value#$cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin'(s))
}
function {:inline} $IsEqual'$cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin''(s1: $cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin', s2: $cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin'): bool {
    s1 == s2
}

// struct BasicCoin::Coin<#0> at .\sources\FirstModule.move:10:5+69
type {:datatype} $cafe_BasicCoin_Coin'#0';
function {:constructor} $cafe_BasicCoin_Coin'#0'($value: int): $cafe_BasicCoin_Coin'#0';
function {:inline} $Update'$cafe_BasicCoin_Coin'#0''_value(s: $cafe_BasicCoin_Coin'#0', x: int): $cafe_BasicCoin_Coin'#0' {
    $cafe_BasicCoin_Coin'#0'(x)
}
function $IsValid'$cafe_BasicCoin_Coin'#0''(s: $cafe_BasicCoin_Coin'#0'): bool {
    $IsValid'u64'($value#$cafe_BasicCoin_Coin'#0'(s))
}
function {:inline} $IsEqual'$cafe_BasicCoin_Coin'#0''(s1: $cafe_BasicCoin_Coin'#0', s2: $cafe_BasicCoin_Coin'#0'): bool {
    s1 == s2
}

// fun BasicCoin::balance_of<MyOddCoin::MyOddCoin> [baseline] at .\sources\FirstModule.move:28:5+138
procedure {:inline 1} $cafe_BasicCoin_balance_of'$cafe_MyOddCoin_MyOddCoin'(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t1: $cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin';
    var $t2: int;
    var $t3: $cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin';
    var $t4: int;
    var $t0: int;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[owner]($t0) at .\sources\FirstModule.move:28:5+1
    assume {:print "$at(2,862,863)"} true;
    assume {:print "$track_local(1,0,0):", $t0} $t0 == $t0;

    // $t1 := get_global<BasicCoin::Balance<#0>>($t0) on_abort goto L2 with $t2 at .\sources\FirstModule.move:29:9+13
    assume {:print "$at(2,943,956)"} true;
    if (!$ResourceExists($cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t1 := $ResourceValue($cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin'_$memory, $t0);
    }
    if ($abort_flag) {
        assume {:print "$at(2,943,956)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(1,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t3 := get_field<BasicCoin::Balance<#0>>.coin($t1) at .\sources\FirstModule.move:29:9+44
    $t3 := $coin#$cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin'($t1);

    // $t4 := get_field<BasicCoin::Coin<#0>>.value($t3) at .\sources\FirstModule.move:29:9+50
    $t4 := $value#$cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin'($t3);

    // trace_return[0]($t4) at .\sources\FirstModule.move:29:9+50
    assume {:print "$track_return(1,0,0):", $t4} $t4 == $t4;

    // label L1 at .\sources\FirstModule.move:30:5+1
    assume {:print "$at(2,999,1000)"} true;
L1:

    // return $t4 at .\sources\FirstModule.move:30:5+1
    assume {:print "$at(2,999,1000)"} true;
    $ret0 := $t4;
    return;

    // label L2 at .\sources\FirstModule.move:30:5+1
L2:

    // abort($t2) at .\sources\FirstModule.move:30:5+1
    assume {:print "$at(2,999,1000)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun BasicCoin::balance_of<#0> [baseline] at .\sources\FirstModule.move:28:5+138
procedure {:inline 1} $cafe_BasicCoin_balance_of'#0'(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t1: $cafe_BasicCoin_Balance'#0';
    var $t2: int;
    var $t3: $cafe_BasicCoin_Coin'#0';
    var $t4: int;
    var $t0: int;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[owner]($t0) at .\sources\FirstModule.move:28:5+1
    assume {:print "$at(2,862,863)"} true;
    assume {:print "$track_local(1,0,0):", $t0} $t0 == $t0;

    // $t1 := get_global<BasicCoin::Balance<#0>>($t0) on_abort goto L2 with $t2 at .\sources\FirstModule.move:29:9+13
    assume {:print "$at(2,943,956)"} true;
    if (!$ResourceExists($cafe_BasicCoin_Balance'#0'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t1 := $ResourceValue($cafe_BasicCoin_Balance'#0'_$memory, $t0);
    }
    if ($abort_flag) {
        assume {:print "$at(2,943,956)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(1,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t3 := get_field<BasicCoin::Balance<#0>>.coin($t1) at .\sources\FirstModule.move:29:9+44
    $t3 := $coin#$cafe_BasicCoin_Balance'#0'($t1);

    // $t4 := get_field<BasicCoin::Coin<#0>>.value($t3) at .\sources\FirstModule.move:29:9+50
    $t4 := $value#$cafe_BasicCoin_Coin'#0'($t3);

    // trace_return[0]($t4) at .\sources\FirstModule.move:29:9+50
    assume {:print "$track_return(1,0,0):", $t4} $t4 == $t4;

    // label L1 at .\sources\FirstModule.move:30:5+1
    assume {:print "$at(2,999,1000)"} true;
L1:

    // return $t4 at .\sources\FirstModule.move:30:5+1
    assume {:print "$at(2,999,1000)"} true;
    $ret0 := $t4;
    return;

    // label L2 at .\sources\FirstModule.move:30:5+1
L2:

    // abort($t2) at .\sources\FirstModule.move:30:5+1
    assume {:print "$at(2,999,1000)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun BasicCoin::balance_of [verification] at .\sources\FirstModule.move:28:5+138
procedure {:timeLimit 40} $cafe_BasicCoin_balance_of$verify(_$t0: int) returns ($ret0: int)
{
    // declare local variables
    var $t1: $cafe_BasicCoin_Balance'#0';
    var $t2: int;
    var $t3: $cafe_BasicCoin_Coin'#0';
    var $t4: int;
    var $t0: int;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at .\sources\FirstModule.move:28:5+1
    assume {:print "$at(2,862,863)"} true;
    assume $IsValid'address'($t0);

    // assume forall $rsc: ResourceDomain<BasicCoin::Balance<#0>>(): WellFormed($rsc) at .\sources\FirstModule.move:28:5+1
    assume (forall $a_0: int :: {$ResourceValue($cafe_BasicCoin_Balance'#0'_$memory, $a_0)}(var $rsc := $ResourceValue($cafe_BasicCoin_Balance'#0'_$memory, $a_0);
    ($IsValid'$cafe_BasicCoin_Balance'#0''($rsc))));

    // trace_local[owner]($t0) at .\sources\FirstModule.move:28:5+1
    assume {:print "$track_local(1,0,0):", $t0} $t0 == $t0;

    // $t1 := get_global<BasicCoin::Balance<#0>>($t0) on_abort goto L2 with $t2 at .\sources\FirstModule.move:29:9+13
    assume {:print "$at(2,943,956)"} true;
    if (!$ResourceExists($cafe_BasicCoin_Balance'#0'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t1 := $ResourceValue($cafe_BasicCoin_Balance'#0'_$memory, $t0);
    }
    if ($abort_flag) {
        assume {:print "$at(2,943,956)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(1,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t3 := get_field<BasicCoin::Balance<#0>>.coin($t1) at .\sources\FirstModule.move:29:9+44
    $t3 := $coin#$cafe_BasicCoin_Balance'#0'($t1);

    // $t4 := get_field<BasicCoin::Coin<#0>>.value($t3) at .\sources\FirstModule.move:29:9+50
    $t4 := $value#$cafe_BasicCoin_Coin'#0'($t3);

    // trace_return[0]($t4) at .\sources\FirstModule.move:29:9+50
    assume {:print "$track_return(1,0,0):", $t4} $t4 == $t4;

    // label L1 at .\sources\FirstModule.move:30:5+1
    assume {:print "$at(2,999,1000)"} true;
L1:

    // assert Not(false) at .\sources\FirstModule.move:30:5+1
    assume {:print "$at(2,999,1000)"} true;
    assert {:msg "assert_failed(2,999,1000): function does not abort under this condition"}
      !false;

    // return $t4 at .\sources\FirstModule.move:30:5+1
    $ret0 := $t4;
    return;

    // label L2 at .\sources\FirstModule.move:30:5+1
L2:

    // assert false at .\sources\FirstModule.move:32:5+60
    assume {:print "$at(2,1008,1068)"} true;
    assert {:msg "assert_failed(2,1008,1068): abort not covered by any of the `aborts_if` clauses"}
      false;

    // abort($t2) at .\sources\FirstModule.move:32:5+60
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun BasicCoin::deposit<MyOddCoin::MyOddCoin> [baseline] at .\sources\FirstModule.move:49:5+298
procedure {:inline 1} $cafe_BasicCoin_deposit'$cafe_MyOddCoin_MyOddCoin'(_$t0: int, _$t1: $cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin') returns ()
{
    // declare local variables
    var $t2: int;
    var $t3: $Mutation (int);
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: $Mutation ($cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin');
    var $t8: $Mutation ($cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin');
    var $t9: $Mutation (int);
    var $t10: int;
    var $t11: int;
    var $t0: int;
    var $t1: $cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin';
    var $temp_0'$cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin'': $cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[addr]($t0) at .\sources\FirstModule.move:49:5+1
    assume {:print "$at(2,1703,1704)"} true;
    assume {:print "$track_local(1,1,0):", $t0} $t0 == $t0;

    // trace_local[check]($t1) at .\sources\FirstModule.move:49:5+1
    assume {:print "$track_local(1,1,1):", $t1} $t1 == $t1;

    // $t5 := BasicCoin::balance_of<#0>($t0) on_abort goto L2 with $t6 at .\sources\FirstModule.move:50:23+26
    assume {:print "$at(2,1804,1830)"} true;
    call $t5 := $cafe_BasicCoin_balance_of'$cafe_MyOddCoin_MyOddCoin'($t0);
    if ($abort_flag) {
        assume {:print "$at(2,1804,1830)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,1):", $t6} $t6 == $t6;
        goto L2;
    }

    // trace_local[balance]($t5) at .\sources\FirstModule.move:50:13+7
    assume {:print "$track_local(1,1,2):", $t5} $t5 == $t5;

    // $t7 := borrow_global<BasicCoin::Balance<#0>>($t0) on_abort goto L2 with $t6 at .\sources\FirstModule.move:51:32+17
    assume {:print "$at(2,1864,1881)"} true;
    if (!$ResourceExists($cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t7 := $Mutation($Global($t0), EmptyVec(), $ResourceValue($cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin'_$memory, $t0));
    }
    if ($abort_flag) {
        assume {:print "$at(2,1864,1881)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,1):", $t6} $t6 == $t6;
        goto L2;
    }

    // $t8 := borrow_field<BasicCoin::Balance<#0>>.coin($t7) at .\sources\FirstModule.move:51:32+47
    $t8 := $ChildMutation($t7, 0, $coin#$cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin'($Dereference($t7)));

    // $t9 := borrow_field<BasicCoin::Coin<#0>>.value($t8) at .\sources\FirstModule.move:51:27+58
    $t9 := $ChildMutation($t8, 0, $value#$cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin'($Dereference($t8)));

    // trace_local[balance_ref]($t9) at .\sources\FirstModule.move:51:13+11
    $temp_0'u64' := $Dereference($t9);
    assume {:print "$track_local(1,1,3):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // $t10 := unpack BasicCoin::Coin<#0>($t1) at .\sources\FirstModule.move:52:13+12
    assume {:print "$at(2,1932,1944)"} true;
    $t10 := $value#$cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin'($t1);

    // trace_local[value]($t10) at .\sources\FirstModule.move:52:19+5
    assume {:print "$track_local(1,1,4):", $t10} $t10 == $t10;

    // $t11 := +($t5, $t10) on_abort goto L2 with $t6 at .\sources\FirstModule.move:53:32+1
    assume {:print "$at(2,1986,1987)"} true;
    call $t11 := $AddU64($t5, $t10);
    if ($abort_flag) {
        assume {:print "$at(2,1986,1987)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,1):", $t6} $t6 == $t6;
        goto L2;
    }

    // write_ref($t9, $t11) at .\sources\FirstModule.move:53:9+30
    $t9 := $UpdateMutation($t9, $t11);

    // write_back[Reference($t8).value (u64)]($t9) at .\sources\FirstModule.move:53:9+30
    $t8 := $UpdateMutation($t8, $Update'$cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin''_value($Dereference($t8), $Dereference($t9)));

    // write_back[Reference($t7).coin (BasicCoin::Coin<#0>)]($t8) at .\sources\FirstModule.move:53:9+30
    $t7 := $UpdateMutation($t7, $Update'$cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin''_coin($Dereference($t7), $Dereference($t8)));

    // write_back[BasicCoin::Balance<#0>@]($t7) at .\sources\FirstModule.move:53:9+30
    $cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin'_$memory := $ResourceUpdate($cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin'_$memory, $GlobalLocationAddress($t7),
        $Dereference($t7));

    // label L1 at .\sources\FirstModule.move:54:5+1
    assume {:print "$at(2,2000,2001)"} true;
L1:

    // return () at .\sources\FirstModule.move:54:5+1
    assume {:print "$at(2,2000,2001)"} true;
    return;

    // label L2 at .\sources\FirstModule.move:54:5+1
L2:

    // abort($t6) at .\sources\FirstModule.move:54:5+1
    assume {:print "$at(2,2000,2001)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun BasicCoin::deposit<#0> [baseline] at .\sources\FirstModule.move:49:5+298
procedure {:inline 1} $cafe_BasicCoin_deposit'#0'(_$t0: int, _$t1: $cafe_BasicCoin_Coin'#0') returns ()
{
    // declare local variables
    var $t2: int;
    var $t3: $Mutation (int);
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: $Mutation ($cafe_BasicCoin_Balance'#0');
    var $t8: $Mutation ($cafe_BasicCoin_Coin'#0');
    var $t9: $Mutation (int);
    var $t10: int;
    var $t11: int;
    var $t0: int;
    var $t1: $cafe_BasicCoin_Coin'#0';
    var $temp_0'$cafe_BasicCoin_Coin'#0'': $cafe_BasicCoin_Coin'#0';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[addr]($t0) at .\sources\FirstModule.move:49:5+1
    assume {:print "$at(2,1703,1704)"} true;
    assume {:print "$track_local(1,1,0):", $t0} $t0 == $t0;

    // trace_local[check]($t1) at .\sources\FirstModule.move:49:5+1
    assume {:print "$track_local(1,1,1):", $t1} $t1 == $t1;

    // $t5 := BasicCoin::balance_of<#0>($t0) on_abort goto L2 with $t6 at .\sources\FirstModule.move:50:23+26
    assume {:print "$at(2,1804,1830)"} true;
    call $t5 := $cafe_BasicCoin_balance_of'#0'($t0);
    if ($abort_flag) {
        assume {:print "$at(2,1804,1830)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,1):", $t6} $t6 == $t6;
        goto L2;
    }

    // trace_local[balance]($t5) at .\sources\FirstModule.move:50:13+7
    assume {:print "$track_local(1,1,2):", $t5} $t5 == $t5;

    // $t7 := borrow_global<BasicCoin::Balance<#0>>($t0) on_abort goto L2 with $t6 at .\sources\FirstModule.move:51:32+17
    assume {:print "$at(2,1864,1881)"} true;
    if (!$ResourceExists($cafe_BasicCoin_Balance'#0'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t7 := $Mutation($Global($t0), EmptyVec(), $ResourceValue($cafe_BasicCoin_Balance'#0'_$memory, $t0));
    }
    if ($abort_flag) {
        assume {:print "$at(2,1864,1881)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,1):", $t6} $t6 == $t6;
        goto L2;
    }

    // $t8 := borrow_field<BasicCoin::Balance<#0>>.coin($t7) at .\sources\FirstModule.move:51:32+47
    $t8 := $ChildMutation($t7, 0, $coin#$cafe_BasicCoin_Balance'#0'($Dereference($t7)));

    // $t9 := borrow_field<BasicCoin::Coin<#0>>.value($t8) at .\sources\FirstModule.move:51:27+58
    $t9 := $ChildMutation($t8, 0, $value#$cafe_BasicCoin_Coin'#0'($Dereference($t8)));

    // trace_local[balance_ref]($t9) at .\sources\FirstModule.move:51:13+11
    $temp_0'u64' := $Dereference($t9);
    assume {:print "$track_local(1,1,3):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // $t10 := unpack BasicCoin::Coin<#0>($t1) at .\sources\FirstModule.move:52:13+12
    assume {:print "$at(2,1932,1944)"} true;
    $t10 := $value#$cafe_BasicCoin_Coin'#0'($t1);

    // trace_local[value]($t10) at .\sources\FirstModule.move:52:19+5
    assume {:print "$track_local(1,1,4):", $t10} $t10 == $t10;

    // $t11 := +($t5, $t10) on_abort goto L2 with $t6 at .\sources\FirstModule.move:53:32+1
    assume {:print "$at(2,1986,1987)"} true;
    call $t11 := $AddU64($t5, $t10);
    if ($abort_flag) {
        assume {:print "$at(2,1986,1987)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,1):", $t6} $t6 == $t6;
        goto L2;
    }

    // write_ref($t9, $t11) at .\sources\FirstModule.move:53:9+30
    $t9 := $UpdateMutation($t9, $t11);

    // write_back[Reference($t8).value (u64)]($t9) at .\sources\FirstModule.move:53:9+30
    $t8 := $UpdateMutation($t8, $Update'$cafe_BasicCoin_Coin'#0''_value($Dereference($t8), $Dereference($t9)));

    // write_back[Reference($t7).coin (BasicCoin::Coin<#0>)]($t8) at .\sources\FirstModule.move:53:9+30
    $t7 := $UpdateMutation($t7, $Update'$cafe_BasicCoin_Balance'#0''_coin($Dereference($t7), $Dereference($t8)));

    // write_back[BasicCoin::Balance<#0>@]($t7) at .\sources\FirstModule.move:53:9+30
    $cafe_BasicCoin_Balance'#0'_$memory := $ResourceUpdate($cafe_BasicCoin_Balance'#0'_$memory, $GlobalLocationAddress($t7),
        $Dereference($t7));

    // label L1 at .\sources\FirstModule.move:54:5+1
    assume {:print "$at(2,2000,2001)"} true;
L1:

    // return () at .\sources\FirstModule.move:54:5+1
    assume {:print "$at(2,2000,2001)"} true;
    return;

    // label L2 at .\sources\FirstModule.move:54:5+1
L2:

    // abort($t6) at .\sources\FirstModule.move:54:5+1
    assume {:print "$at(2,2000,2001)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun BasicCoin::deposit [verification] at .\sources\FirstModule.move:49:5+298
procedure {:timeLimit 40} $cafe_BasicCoin_deposit$verify(_$t0: int, _$t1: $cafe_BasicCoin_Coin'#0') returns ()
{
    // declare local variables
    var $t2: int;
    var $t3: $Mutation (int);
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: $Mutation ($cafe_BasicCoin_Balance'#0');
    var $t8: $Mutation ($cafe_BasicCoin_Coin'#0');
    var $t9: $Mutation (int);
    var $t10: int;
    var $t11: int;
    var $t0: int;
    var $t1: $cafe_BasicCoin_Coin'#0';
    var $temp_0'$cafe_BasicCoin_Coin'#0'': $cafe_BasicCoin_Coin'#0';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at .\sources\FirstModule.move:49:5+1
    assume {:print "$at(2,1703,1704)"} true;
    assume $IsValid'address'($t0);

    // assume WellFormed($t1) at .\sources\FirstModule.move:49:5+1
    assume $IsValid'$cafe_BasicCoin_Coin'#0''($t1);

    // assume forall $rsc: ResourceDomain<BasicCoin::Balance<#0>>(): WellFormed($rsc) at .\sources\FirstModule.move:49:5+1
    assume (forall $a_0: int :: {$ResourceValue($cafe_BasicCoin_Balance'#0'_$memory, $a_0)}(var $rsc := $ResourceValue($cafe_BasicCoin_Balance'#0'_$memory, $a_0);
    ($IsValid'$cafe_BasicCoin_Balance'#0''($rsc))));

    // trace_local[addr]($t0) at .\sources\FirstModule.move:49:5+1
    assume {:print "$track_local(1,1,0):", $t0} $t0 == $t0;

    // trace_local[check]($t1) at .\sources\FirstModule.move:49:5+1
    assume {:print "$track_local(1,1,1):", $t1} $t1 == $t1;

    // $t5 := BasicCoin::balance_of<#0>($t0) on_abort goto L2 with $t6 at .\sources\FirstModule.move:50:23+26
    assume {:print "$at(2,1804,1830)"} true;
    call $t5 := $cafe_BasicCoin_balance_of'#0'($t0);
    if ($abort_flag) {
        assume {:print "$at(2,1804,1830)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,1):", $t6} $t6 == $t6;
        goto L2;
    }

    // trace_local[balance]($t5) at .\sources\FirstModule.move:50:13+7
    assume {:print "$track_local(1,1,2):", $t5} $t5 == $t5;

    // $t7 := borrow_global<BasicCoin::Balance<#0>>($t0) on_abort goto L2 with $t6 at .\sources\FirstModule.move:51:32+17
    assume {:print "$at(2,1864,1881)"} true;
    if (!$ResourceExists($cafe_BasicCoin_Balance'#0'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t7 := $Mutation($Global($t0), EmptyVec(), $ResourceValue($cafe_BasicCoin_Balance'#0'_$memory, $t0));
    }
    if ($abort_flag) {
        assume {:print "$at(2,1864,1881)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,1):", $t6} $t6 == $t6;
        goto L2;
    }

    // $t8 := borrow_field<BasicCoin::Balance<#0>>.coin($t7) at .\sources\FirstModule.move:51:32+47
    $t8 := $ChildMutation($t7, 0, $coin#$cafe_BasicCoin_Balance'#0'($Dereference($t7)));

    // $t9 := borrow_field<BasicCoin::Coin<#0>>.value($t8) at .\sources\FirstModule.move:51:27+58
    $t9 := $ChildMutation($t8, 0, $value#$cafe_BasicCoin_Coin'#0'($Dereference($t8)));

    // trace_local[balance_ref]($t9) at .\sources\FirstModule.move:51:13+11
    $temp_0'u64' := $Dereference($t9);
    assume {:print "$track_local(1,1,3):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // $t10 := unpack BasicCoin::Coin<#0>($t1) at .\sources\FirstModule.move:52:13+12
    assume {:print "$at(2,1932,1944)"} true;
    $t10 := $value#$cafe_BasicCoin_Coin'#0'($t1);

    // trace_local[value]($t10) at .\sources\FirstModule.move:52:19+5
    assume {:print "$track_local(1,1,4):", $t10} $t10 == $t10;

    // $t11 := +($t5, $t10) on_abort goto L2 with $t6 at .\sources\FirstModule.move:53:32+1
    assume {:print "$at(2,1986,1987)"} true;
    call $t11 := $AddU64($t5, $t10);
    if ($abort_flag) {
        assume {:print "$at(2,1986,1987)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,1):", $t6} $t6 == $t6;
        goto L2;
    }

    // write_ref($t9, $t11) at .\sources\FirstModule.move:53:9+30
    $t9 := $UpdateMutation($t9, $t11);

    // write_back[Reference($t8).value (u64)]($t9) at .\sources\FirstModule.move:53:9+30
    $t8 := $UpdateMutation($t8, $Update'$cafe_BasicCoin_Coin'#0''_value($Dereference($t8), $Dereference($t9)));

    // write_back[Reference($t7).coin (BasicCoin::Coin<#0>)]($t8) at .\sources\FirstModule.move:53:9+30
    $t7 := $UpdateMutation($t7, $Update'$cafe_BasicCoin_Balance'#0''_coin($Dereference($t7), $Dereference($t8)));

    // write_back[BasicCoin::Balance<#0>@]($t7) at .\sources\FirstModule.move:53:9+30
    $cafe_BasicCoin_Balance'#0'_$memory := $ResourceUpdate($cafe_BasicCoin_Balance'#0'_$memory, $GlobalLocationAddress($t7),
        $Dereference($t7));

    // label L1 at .\sources\FirstModule.move:54:5+1
    assume {:print "$at(2,2000,2001)"} true;
L1:

    // return () at .\sources\FirstModule.move:54:5+1
    assume {:print "$at(2,2000,2001)"} true;
    return;

    // label L2 at .\sources\FirstModule.move:54:5+1
L2:

    // abort($t6) at .\sources\FirstModule.move:54:5+1
    assume {:print "$at(2,2000,2001)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun BasicCoin::mint<MyOddCoin::MyOddCoin> [baseline] at .\sources\FirstModule.move:24:5+170
procedure {:inline 1} $cafe_BasicCoin_mint'$cafe_MyOddCoin_MyOddCoin'(_$t0: int, _$t1: int, _$t2: $cafe_MyOddCoin_MyOddCoin) returns ()
{
    // declare local variables
    var $t3: $cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin';
    var $t4: int;
    var $t0: int;
    var $t1: int;
    var $t2: $cafe_MyOddCoin_MyOddCoin;
    var $temp_0'$cafe_MyOddCoin_MyOddCoin': $cafe_MyOddCoin_MyOddCoin;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // bytecode translation starts here
    // trace_local[mint_addr]($t0) at .\sources\FirstModule.move:24:5+1
    assume {:print "$at(2,684,685)"} true;
    assume {:print "$track_local(1,2,0):", $t0} $t0 == $t0;

    // trace_local[amount]($t1) at .\sources\FirstModule.move:24:5+1
    assume {:print "$track_local(1,2,1):", $t1} $t1 == $t1;

    // trace_local[_witness]($t2) at .\sources\FirstModule.move:24:5+1
    assume {:print "$track_local(1,2,2):", $t2} $t2 == $t2;

    // $t3 := pack BasicCoin::Coin<#0>($t1) at .\sources\FirstModule.move:25:28+29
    assume {:print "$at(2,816,845)"} true;
    $t3 := $cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin'($t1);

    // BasicCoin::deposit<#0>($t0, $t3) on_abort goto L2 with $t4 at .\sources\FirstModule.move:25:9+49
    call $cafe_BasicCoin_deposit'$cafe_MyOddCoin_MyOddCoin'($t0, $t3);
    if ($abort_flag) {
        assume {:print "$at(2,797,846)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(1,2):", $t4} $t4 == $t4;
        goto L2;
    }

    // label L1 at .\sources\FirstModule.move:26:5+1
    assume {:print "$at(2,853,854)"} true;
L1:

    // return () at .\sources\FirstModule.move:26:5+1
    assume {:print "$at(2,853,854)"} true;
    return;

    // label L2 at .\sources\FirstModule.move:26:5+1
L2:

    // abort($t4) at .\sources\FirstModule.move:26:5+1
    assume {:print "$at(2,853,854)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun BasicCoin::mint [verification] at .\sources\FirstModule.move:24:5+170
procedure {:timeLimit 40} $cafe_BasicCoin_mint$verify(_$t0: int, _$t1: int, _$t2: #0) returns ()
{
    // declare local variables
    var $t3: $cafe_BasicCoin_Coin'#0';
    var $t4: int;
    var $t0: int;
    var $t1: int;
    var $t2: #0;
    var $temp_0'#0': #0;
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at .\sources\FirstModule.move:24:5+1
    assume {:print "$at(2,684,685)"} true;
    assume $IsValid'address'($t0);

    // assume WellFormed($t1) at .\sources\FirstModule.move:24:5+1
    assume $IsValid'u64'($t1);

    // assume WellFormed($t2) at .\sources\FirstModule.move:24:5+1
    assume $IsValid'#0'($t2);

    // assume forall $rsc: ResourceDomain<BasicCoin::Balance<#0>>(): WellFormed($rsc) at .\sources\FirstModule.move:24:5+1
    assume (forall $a_0: int :: {$ResourceValue($cafe_BasicCoin_Balance'#0'_$memory, $a_0)}(var $rsc := $ResourceValue($cafe_BasicCoin_Balance'#0'_$memory, $a_0);
    ($IsValid'$cafe_BasicCoin_Balance'#0''($rsc))));

    // trace_local[mint_addr]($t0) at .\sources\FirstModule.move:24:5+1
    assume {:print "$track_local(1,2,0):", $t0} $t0 == $t0;

    // trace_local[amount]($t1) at .\sources\FirstModule.move:24:5+1
    assume {:print "$track_local(1,2,1):", $t1} $t1 == $t1;

    // trace_local[_witness]($t2) at .\sources\FirstModule.move:24:5+1
    assume {:print "$track_local(1,2,2):", $t2} $t2 == $t2;

    // $t3 := pack BasicCoin::Coin<#0>($t1) at .\sources\FirstModule.move:25:28+29
    assume {:print "$at(2,816,845)"} true;
    $t3 := $cafe_BasicCoin_Coin'#0'($t1);

    // BasicCoin::deposit<#0>($t0, $t3) on_abort goto L2 with $t4 at .\sources\FirstModule.move:25:9+49
    call $cafe_BasicCoin_deposit'#0'($t0, $t3);
    if ($abort_flag) {
        assume {:print "$at(2,797,846)"} true;
        $t4 := $abort_code;
        assume {:print "$track_abort(1,2):", $t4} $t4 == $t4;
        goto L2;
    }

    // label L1 at .\sources\FirstModule.move:26:5+1
    assume {:print "$at(2,853,854)"} true;
L1:

    // return () at .\sources\FirstModule.move:26:5+1
    assume {:print "$at(2,853,854)"} true;
    return;

    // label L2 at .\sources\FirstModule.move:26:5+1
L2:

    // abort($t4) at .\sources\FirstModule.move:26:5+1
    assume {:print "$at(2,853,854)"} true;
    $abort_code := $t4;
    $abort_flag := true;
    return;

}

// fun BasicCoin::publish_balance<MyOddCoin::MyOddCoin> [baseline] at .\sources\FirstModule.move:18:5+275
procedure {:inline 1} $cafe_BasicCoin_publish_balance'$cafe_MyOddCoin_MyOddCoin'(_$t0: $signer) returns ()
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: bool;
    var $t4: bool;
    var $t5: int;
    var $t6: int;
    var $t7: $cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin';
    var $t8: $cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin';
    var $t0: $signer;
    var $temp_0'signer': $signer;
    $t0 := _$t0;

    // bytecode translation starts here
    // trace_local[account]($t0) at .\sources\FirstModule.move:18:5+1
    assume {:print "$at(2,401,402)"} true;
    assume {:print "$track_local(1,3,0):", $t0} $t0 == $t0;

    // $t1 := signer::address_of($t0) on_abort goto L4 with $t2 at .\sources\FirstModule.move:20:44+27
    assume {:print "$at(2,554,581)"} true;
    call $t1 := $1_signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(2,554,581)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(1,3):", $t2} $t2 == $t2;
        goto L4;
    }

    // $t3 := exists<BasicCoin::Balance<#0>>($t1) at .\sources\FirstModule.move:20:18+6
    $t3 := $ResourceExists($cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin'_$memory, $t1);

    // $t4 := !($t3) at .\sources\FirstModule.move:20:17+1
    call $t4 := $Not($t3);

    // if ($t4) goto L1 else goto L0 at .\sources\FirstModule.move:20:9+85
    if ($t4) { goto L1; } else { goto L0; }

    // label L1 at .\sources\FirstModule.move:20:9+85
L1:

    // goto L2 at .\sources\FirstModule.move:20:9+85
    assume {:print "$at(2,519,604)"} true;
    goto L2;

    // label L0 at .\sources\FirstModule.move:20:9+85
L0:

    // $t5 := 2 at .\sources\FirstModule.move:20:73+20
    assume {:print "$at(2,583,603)"} true;
    $t5 := 2;
    assume $IsValid'u64'($t5);

    // trace_abort($t5) at .\sources\FirstModule.move:20:9+85
    assume {:print "$at(2,519,604)"} true;
    assume {:print "$track_abort(1,3):", $t5} $t5 == $t5;

    // $t2 := move($t5) at .\sources\FirstModule.move:20:9+85
    $t2 := $t5;

    // goto L4 at .\sources\FirstModule.move:20:9+85
    goto L4;

    // label L2 at .\sources\FirstModule.move:21:17+7
    assume {:print "$at(2,623,630)"} true;
L2:

    // $t6 := 0 at .\sources\FirstModule.move:19:48+1
    assume {:print "$at(2,506,507)"} true;
    $t6 := 0;
    assume $IsValid'u64'($t6);

    // $t7 := pack BasicCoin::Coin<#0>($t6) at .\sources\FirstModule.move:19:26+24
    $t7 := $cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin'($t6);

    // $t8 := pack BasicCoin::Balance<#0>($t7) at .\sources\FirstModule.move:21:26+35
    assume {:print "$at(2,632,667)"} true;
    $t8 := $cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin'($t7);

    // move_to<BasicCoin::Balance<#0>>($t8, $t0) on_abort goto L4 with $t2 at .\sources\FirstModule.move:21:9+7
    if ($ResourceExists($cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin'_$memory, $addr#$signer($t0))) {
        call $ExecFailureAbort();
    } else {
        $cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin'_$memory := $ResourceUpdate($cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin'_$memory, $addr#$signer($t0), $t8);
    }
    if ($abort_flag) {
        assume {:print "$at(2,615,622)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(1,3):", $t2} $t2 == $t2;
        goto L4;
    }

    // label L3 at .\sources\FirstModule.move:22:5+1
    assume {:print "$at(2,675,676)"} true;
L3:

    // return () at .\sources\FirstModule.move:22:5+1
    assume {:print "$at(2,675,676)"} true;
    return;

    // label L4 at .\sources\FirstModule.move:22:5+1
L4:

    // abort($t2) at .\sources\FirstModule.move:22:5+1
    assume {:print "$at(2,675,676)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun BasicCoin::publish_balance [verification] at .\sources\FirstModule.move:18:5+275
procedure {:timeLimit 40} $cafe_BasicCoin_publish_balance$verify(_$t0: $signer) returns ()
{
    // declare local variables
    var $t1: int;
    var $t2: int;
    var $t3: bool;
    var $t4: bool;
    var $t5: int;
    var $t6: int;
    var $t7: $cafe_BasicCoin_Coin'#0';
    var $t8: $cafe_BasicCoin_Balance'#0';
    var $t0: $signer;
    var $temp_0'signer': $signer;
    $t0 := _$t0;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at .\sources\FirstModule.move:18:5+1
    assume {:print "$at(2,401,402)"} true;
    assume $IsValid'signer'($t0) && $1_signer_is_txn_signer($t0) && $1_signer_is_txn_signer_addr($addr#$signer($t0));

    // assume forall $rsc: ResourceDomain<BasicCoin::Balance<#0>>(): WellFormed($rsc) at .\sources\FirstModule.move:18:5+1
    assume (forall $a_0: int :: {$ResourceValue($cafe_BasicCoin_Balance'#0'_$memory, $a_0)}(var $rsc := $ResourceValue($cafe_BasicCoin_Balance'#0'_$memory, $a_0);
    ($IsValid'$cafe_BasicCoin_Balance'#0''($rsc))));

    // trace_local[account]($t0) at .\sources\FirstModule.move:18:5+1
    assume {:print "$track_local(1,3,0):", $t0} $t0 == $t0;

    // $t1 := signer::address_of($t0) on_abort goto L4 with $t2 at .\sources\FirstModule.move:20:44+27
    assume {:print "$at(2,554,581)"} true;
    call $t1 := $1_signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(2,554,581)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(1,3):", $t2} $t2 == $t2;
        goto L4;
    }

    // $t3 := exists<BasicCoin::Balance<#0>>($t1) at .\sources\FirstModule.move:20:18+6
    $t3 := $ResourceExists($cafe_BasicCoin_Balance'#0'_$memory, $t1);

    // $t4 := !($t3) at .\sources\FirstModule.move:20:17+1
    call $t4 := $Not($t3);

    // if ($t4) goto L1 else goto L0 at .\sources\FirstModule.move:20:9+85
    if ($t4) { goto L1; } else { goto L0; }

    // label L1 at .\sources\FirstModule.move:20:9+85
L1:

    // goto L2 at .\sources\FirstModule.move:20:9+85
    assume {:print "$at(2,519,604)"} true;
    goto L2;

    // label L0 at .\sources\FirstModule.move:20:9+85
L0:

    // $t5 := 2 at .\sources\FirstModule.move:20:73+20
    assume {:print "$at(2,583,603)"} true;
    $t5 := 2;
    assume $IsValid'u64'($t5);

    // trace_abort($t5) at .\sources\FirstModule.move:20:9+85
    assume {:print "$at(2,519,604)"} true;
    assume {:print "$track_abort(1,3):", $t5} $t5 == $t5;

    // $t2 := move($t5) at .\sources\FirstModule.move:20:9+85
    $t2 := $t5;

    // goto L4 at .\sources\FirstModule.move:20:9+85
    goto L4;

    // label L2 at .\sources\FirstModule.move:21:17+7
    assume {:print "$at(2,623,630)"} true;
L2:

    // $t6 := 0 at .\sources\FirstModule.move:19:48+1
    assume {:print "$at(2,506,507)"} true;
    $t6 := 0;
    assume $IsValid'u64'($t6);

    // $t7 := pack BasicCoin::Coin<#0>($t6) at .\sources\FirstModule.move:19:26+24
    $t7 := $cafe_BasicCoin_Coin'#0'($t6);

    // $t8 := pack BasicCoin::Balance<#0>($t7) at .\sources\FirstModule.move:21:26+35
    assume {:print "$at(2,632,667)"} true;
    $t8 := $cafe_BasicCoin_Balance'#0'($t7);

    // move_to<BasicCoin::Balance<#0>>($t8, $t0) on_abort goto L4 with $t2 at .\sources\FirstModule.move:21:9+7
    if ($ResourceExists($cafe_BasicCoin_Balance'#0'_$memory, $addr#$signer($t0))) {
        call $ExecFailureAbort();
    } else {
        $cafe_BasicCoin_Balance'#0'_$memory := $ResourceUpdate($cafe_BasicCoin_Balance'#0'_$memory, $addr#$signer($t0), $t8);
    }
    if ($abort_flag) {
        assume {:print "$at(2,615,622)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(1,3):", $t2} $t2 == $t2;
        goto L4;
    }

    // label L3 at .\sources\FirstModule.move:22:5+1
    assume {:print "$at(2,675,676)"} true;
L3:

    // return () at .\sources\FirstModule.move:22:5+1
    assume {:print "$at(2,675,676)"} true;
    return;

    // label L4 at .\sources\FirstModule.move:22:5+1
L4:

    // abort($t2) at .\sources\FirstModule.move:22:5+1
    assume {:print "$at(2,675,676)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}

// fun BasicCoin::transfer<MyOddCoin::MyOddCoin> [baseline] at .\sources\FirstModule.move:36:5+236
procedure {:inline 1} $cafe_BasicCoin_transfer'$cafe_MyOddCoin_MyOddCoin'(_$t0: $signer, _$t1: int, _$t2: int, _$t3: $cafe_MyOddCoin_MyOddCoin) returns ()
{
    // declare local variables
    var $t4: $cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin';
    var $t5: int;
    var $t6: int;
    var $t7: $cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin';
    var $t0: $signer;
    var $t1: int;
    var $t2: int;
    var $t3: $cafe_MyOddCoin_MyOddCoin;
    var $temp_0'$cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin'': $cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin';
    var $temp_0'$cafe_MyOddCoin_MyOddCoin': $cafe_MyOddCoin_MyOddCoin;
    var $temp_0'address': int;
    var $temp_0'signer': $signer;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;
    $t3 := _$t3;

    // bytecode translation starts here
    // trace_local[from]($t0) at .\sources\FirstModule.move:36:5+1
    assume {:print "$at(2,1080,1081)"} true;
    assume {:print "$track_local(1,4,0):", $t0} $t0 == $t0;

    // trace_local[to]($t1) at .\sources\FirstModule.move:36:5+1
    assume {:print "$track_local(1,4,1):", $t1} $t1 == $t1;

    // trace_local[amount]($t2) at .\sources\FirstModule.move:36:5+1
    assume {:print "$track_local(1,4,2):", $t2} $t2 == $t2;

    // trace_local[_witness]($t3) at .\sources\FirstModule.move:36:5+1
    assume {:print "$track_local(1,4,3):", $t3} $t3 == $t3;

    // $t5 := signer::address_of($t0) on_abort goto L2 with $t6 at .\sources\FirstModule.move:37:40+24
    assume {:print "$at(2,1236,1260)"} true;
    call $t5 := $1_signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(2,1236,1260)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,4):", $t6} $t6 == $t6;
        goto L2;
    }

    // $t7 := BasicCoin::withdraw<#0>($t5, $t2) on_abort goto L2 with $t6 at .\sources\FirstModule.move:37:21+52
    call $t7 := $cafe_BasicCoin_withdraw'$cafe_MyOddCoin_MyOddCoin'($t5, $t2);
    if ($abort_flag) {
        assume {:print "$at(2,1217,1269)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,4):", $t6} $t6 == $t6;
        goto L2;
    }

    // trace_local[check]($t7) at .\sources\FirstModule.move:37:13+5
    assume {:print "$track_local(1,4,4):", $t7} $t7 == $t7;

    // BasicCoin::deposit<#0>($t1, $t7) on_abort goto L2 with $t6 at .\sources\FirstModule.move:38:9+28
    assume {:print "$at(2,1280,1308)"} true;
    call $cafe_BasicCoin_deposit'$cafe_MyOddCoin_MyOddCoin'($t1, $t7);
    if ($abort_flag) {
        assume {:print "$at(2,1280,1308)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,4):", $t6} $t6 == $t6;
        goto L2;
    }

    // label L1 at .\sources\FirstModule.move:39:5+1
    assume {:print "$at(2,1315,1316)"} true;
L1:

    // return () at .\sources\FirstModule.move:39:5+1
    assume {:print "$at(2,1315,1316)"} true;
    return;

    // label L2 at .\sources\FirstModule.move:39:5+1
L2:

    // abort($t6) at .\sources\FirstModule.move:39:5+1
    assume {:print "$at(2,1315,1316)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun BasicCoin::transfer [verification] at .\sources\FirstModule.move:36:5+236
procedure {:timeLimit 40} $cafe_BasicCoin_transfer$verify(_$t0: $signer, _$t1: int, _$t2: int, _$t3: #0) returns ()
{
    // declare local variables
    var $t4: $cafe_BasicCoin_Coin'#0';
    var $t5: int;
    var $t6: int;
    var $t7: $cafe_BasicCoin_Coin'#0';
    var $t0: $signer;
    var $t1: int;
    var $t2: int;
    var $t3: #0;
    var $temp_0'#0': #0;
    var $temp_0'$cafe_BasicCoin_Coin'#0'': $cafe_BasicCoin_Coin'#0';
    var $temp_0'address': int;
    var $temp_0'signer': $signer;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;
    $t3 := _$t3;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at .\sources\FirstModule.move:36:5+1
    assume {:print "$at(2,1080,1081)"} true;
    assume $IsValid'signer'($t0) && $1_signer_is_txn_signer($t0) && $1_signer_is_txn_signer_addr($addr#$signer($t0));

    // assume WellFormed($t1) at .\sources\FirstModule.move:36:5+1
    assume $IsValid'address'($t1);

    // assume WellFormed($t2) at .\sources\FirstModule.move:36:5+1
    assume $IsValid'u64'($t2);

    // assume WellFormed($t3) at .\sources\FirstModule.move:36:5+1
    assume $IsValid'#0'($t3);

    // assume forall $rsc: ResourceDomain<BasicCoin::Balance<#0>>(): WellFormed($rsc) at .\sources\FirstModule.move:36:5+1
    assume (forall $a_0: int :: {$ResourceValue($cafe_BasicCoin_Balance'#0'_$memory, $a_0)}(var $rsc := $ResourceValue($cafe_BasicCoin_Balance'#0'_$memory, $a_0);
    ($IsValid'$cafe_BasicCoin_Balance'#0''($rsc))));

    // trace_local[from]($t0) at .\sources\FirstModule.move:36:5+1
    assume {:print "$track_local(1,4,0):", $t0} $t0 == $t0;

    // trace_local[to]($t1) at .\sources\FirstModule.move:36:5+1
    assume {:print "$track_local(1,4,1):", $t1} $t1 == $t1;

    // trace_local[amount]($t2) at .\sources\FirstModule.move:36:5+1
    assume {:print "$track_local(1,4,2):", $t2} $t2 == $t2;

    // trace_local[_witness]($t3) at .\sources\FirstModule.move:36:5+1
    assume {:print "$track_local(1,4,3):", $t3} $t3 == $t3;

    // $t5 := signer::address_of($t0) on_abort goto L2 with $t6 at .\sources\FirstModule.move:37:40+24
    assume {:print "$at(2,1236,1260)"} true;
    call $t5 := $1_signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(2,1236,1260)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,4):", $t6} $t6 == $t6;
        goto L2;
    }

    // $t7 := BasicCoin::withdraw<#0>($t5, $t2) on_abort goto L2 with $t6 at .\sources\FirstModule.move:37:21+52
    call $t7 := $cafe_BasicCoin_withdraw'#0'($t5, $t2);
    if ($abort_flag) {
        assume {:print "$at(2,1217,1269)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,4):", $t6} $t6 == $t6;
        goto L2;
    }

    // trace_local[check]($t7) at .\sources\FirstModule.move:37:13+5
    assume {:print "$track_local(1,4,4):", $t7} $t7 == $t7;

    // BasicCoin::deposit<#0>($t1, $t7) on_abort goto L2 with $t6 at .\sources\FirstModule.move:38:9+28
    assume {:print "$at(2,1280,1308)"} true;
    call $cafe_BasicCoin_deposit'#0'($t1, $t7);
    if ($abort_flag) {
        assume {:print "$at(2,1280,1308)"} true;
        $t6 := $abort_code;
        assume {:print "$track_abort(1,4):", $t6} $t6 == $t6;
        goto L2;
    }

    // label L1 at .\sources\FirstModule.move:39:5+1
    assume {:print "$at(2,1315,1316)"} true;
L1:

    // return () at .\sources\FirstModule.move:39:5+1
    assume {:print "$at(2,1315,1316)"} true;
    return;

    // label L2 at .\sources\FirstModule.move:39:5+1
L2:

    // abort($t6) at .\sources\FirstModule.move:39:5+1
    assume {:print "$at(2,1315,1316)"} true;
    $abort_code := $t6;
    $abort_flag := true;
    return;

}

// fun BasicCoin::withdraw<MyOddCoin::MyOddCoin> [baseline] at .\sources\FirstModule.move:41:5+371
procedure {:inline 1} $cafe_BasicCoin_withdraw'$cafe_MyOddCoin_MyOddCoin'(_$t0: int, _$t1: int) returns ($ret0: $cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin')
{
    // declare local variables
    var $t2: int;
    var $t3: $Mutation (int);
    var $t4: int;
    var $t5: int;
    var $t6: bool;
    var $t7: int;
    var $t8: $Mutation ($cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin');
    var $t9: $Mutation ($cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin');
    var $t10: $Mutation (int);
    var $t11: int;
    var $t12: $cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin';
    var $t0: int;
    var $t1: int;
    var $temp_0'$cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin'': $cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[addr]($t0) at .\sources\FirstModule.move:41:5+1
    assume {:print "$at(2,1324,1325)"} true;
    assume {:print "$track_local(1,5,0):", $t0} $t0 == $t0;

    // trace_local[amount]($t1) at .\sources\FirstModule.move:41:5+1
    assume {:print "$track_local(1,5,1):", $t1} $t1 == $t1;

    // $t4 := BasicCoin::balance_of<#0>($t0) on_abort goto L4 with $t5 at .\sources\FirstModule.move:42:23+26
    assume {:print "$at(2,1432,1458)"} true;
    call $t4 := $cafe_BasicCoin_balance_of'$cafe_MyOddCoin_MyOddCoin'($t0);
    if ($abort_flag) {
        assume {:print "$at(2,1432,1458)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(1,5):", $t5} $t5 == $t5;
        goto L4;
    }

    // trace_local[balance]($t4) at .\sources\FirstModule.move:42:13+7
    assume {:print "$track_local(1,5,2):", $t4} $t4 == $t4;

    // $t6 := >=($t4, $t1) at .\sources\FirstModule.move:43:25+2
    assume {:print "$at(2,1485,1487)"} true;
    call $t6 := $Ge($t4, $t1);

    // if ($t6) goto L1 else goto L0 at .\sources\FirstModule.move:43:9+49
    if ($t6) { goto L1; } else { goto L0; }

    // label L1 at .\sources\FirstModule.move:43:9+49
L1:

    // goto L2 at .\sources\FirstModule.move:43:9+49
    assume {:print "$at(2,1469,1518)"} true;
    goto L2;

    // label L0 at .\sources\FirstModule.move:43:36+21
L0:

    // $t7 := 1 at .\sources\FirstModule.move:43:36+21
    assume {:print "$at(2,1496,1517)"} true;
    $t7 := 1;
    assume $IsValid'u64'($t7);

    // trace_abort($t7) at .\sources\FirstModule.move:43:9+49
    assume {:print "$at(2,1469,1518)"} true;
    assume {:print "$track_abort(1,5):", $t7} $t7 == $t7;

    // $t5 := move($t7) at .\sources\FirstModule.move:43:9+49
    $t5 := $t7;

    // goto L4 at .\sources\FirstModule.move:43:9+49
    goto L4;

    // label L2 at .\sources\FirstModule.move:44:69+4
    assume {:print "$at(2,1589,1593)"} true;
L2:

    // $t8 := borrow_global<BasicCoin::Balance<#0>>($t0) on_abort goto L4 with $t5 at .\sources\FirstModule.move:44:32+17
    assume {:print "$at(2,1552,1569)"} true;
    if (!$ResourceExists($cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t8 := $Mutation($Global($t0), EmptyVec(), $ResourceValue($cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin'_$memory, $t0));
    }
    if ($abort_flag) {
        assume {:print "$at(2,1552,1569)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(1,5):", $t5} $t5 == $t5;
        goto L4;
    }

    // $t9 := borrow_field<BasicCoin::Balance<#0>>.coin($t8) at .\sources\FirstModule.move:44:32+47
    $t9 := $ChildMutation($t8, 0, $coin#$cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin'($Dereference($t8)));

    // $t10 := borrow_field<BasicCoin::Coin<#0>>.value($t9) at .\sources\FirstModule.move:44:27+58
    $t10 := $ChildMutation($t9, 0, $value#$cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin'($Dereference($t9)));

    // trace_local[balance_ref]($t10) at .\sources\FirstModule.move:44:13+11
    $temp_0'u64' := $Dereference($t10);
    assume {:print "$track_local(1,5,3):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // $t11 := -($t4, $t1) on_abort goto L4 with $t5 at .\sources\FirstModule.move:45:32+1
    assume {:print "$at(2,1639,1640)"} true;
    call $t11 := $Sub($t4, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,1639,1640)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(1,5):", $t5} $t5 == $t5;
        goto L4;
    }

    // write_ref($t10, $t11) at .\sources\FirstModule.move:45:9+31
    $t10 := $UpdateMutation($t10, $t11);

    // write_back[Reference($t9).value (u64)]($t10) at .\sources\FirstModule.move:45:9+31
    $t9 := $UpdateMutation($t9, $Update'$cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin''_value($Dereference($t9), $Dereference($t10)));

    // write_back[Reference($t8).coin (BasicCoin::Coin<#0>)]($t9) at .\sources\FirstModule.move:45:9+31
    $t8 := $UpdateMutation($t8, $Update'$cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin''_coin($Dereference($t8), $Dereference($t9)));

    // write_back[BasicCoin::Balance<#0>@]($t8) at .\sources\FirstModule.move:45:9+31
    $cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin'_$memory := $ResourceUpdate($cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin'_$memory, $GlobalLocationAddress($t8),
        $Dereference($t8));

    // $t12 := pack BasicCoin::Coin<#0>($t1) at .\sources\FirstModule.move:46:9+30
    assume {:print "$at(2,1658,1688)"} true;
    $t12 := $cafe_BasicCoin_Coin'$cafe_MyOddCoin_MyOddCoin'($t1);

    // trace_return[0]($t12) at .\sources\FirstModule.move:46:9+30
    assume {:print "$track_return(1,5,0):", $t12} $t12 == $t12;

    // label L3 at .\sources\FirstModule.move:47:5+1
    assume {:print "$at(2,1694,1695)"} true;
L3:

    // return $t12 at .\sources\FirstModule.move:47:5+1
    assume {:print "$at(2,1694,1695)"} true;
    $ret0 := $t12;
    return;

    // label L4 at .\sources\FirstModule.move:47:5+1
L4:

    // abort($t5) at .\sources\FirstModule.move:47:5+1
    assume {:print "$at(2,1694,1695)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun BasicCoin::withdraw<#0> [baseline] at .\sources\FirstModule.move:41:5+371
procedure {:inline 1} $cafe_BasicCoin_withdraw'#0'(_$t0: int, _$t1: int) returns ($ret0: $cafe_BasicCoin_Coin'#0')
{
    // declare local variables
    var $t2: int;
    var $t3: $Mutation (int);
    var $t4: int;
    var $t5: int;
    var $t6: bool;
    var $t7: int;
    var $t8: $Mutation ($cafe_BasicCoin_Balance'#0');
    var $t9: $Mutation ($cafe_BasicCoin_Coin'#0');
    var $t10: $Mutation (int);
    var $t11: int;
    var $t12: $cafe_BasicCoin_Coin'#0';
    var $t0: int;
    var $t1: int;
    var $temp_0'$cafe_BasicCoin_Coin'#0'': $cafe_BasicCoin_Coin'#0';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // bytecode translation starts here
    // trace_local[addr]($t0) at .\sources\FirstModule.move:41:5+1
    assume {:print "$at(2,1324,1325)"} true;
    assume {:print "$track_local(1,5,0):", $t0} $t0 == $t0;

    // trace_local[amount]($t1) at .\sources\FirstModule.move:41:5+1
    assume {:print "$track_local(1,5,1):", $t1} $t1 == $t1;

    // $t4 := BasicCoin::balance_of<#0>($t0) on_abort goto L4 with $t5 at .\sources\FirstModule.move:42:23+26
    assume {:print "$at(2,1432,1458)"} true;
    call $t4 := $cafe_BasicCoin_balance_of'#0'($t0);
    if ($abort_flag) {
        assume {:print "$at(2,1432,1458)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(1,5):", $t5} $t5 == $t5;
        goto L4;
    }

    // trace_local[balance]($t4) at .\sources\FirstModule.move:42:13+7
    assume {:print "$track_local(1,5,2):", $t4} $t4 == $t4;

    // $t6 := >=($t4, $t1) at .\sources\FirstModule.move:43:25+2
    assume {:print "$at(2,1485,1487)"} true;
    call $t6 := $Ge($t4, $t1);

    // if ($t6) goto L1 else goto L0 at .\sources\FirstModule.move:43:9+49
    if ($t6) { goto L1; } else { goto L0; }

    // label L1 at .\sources\FirstModule.move:43:9+49
L1:

    // goto L2 at .\sources\FirstModule.move:43:9+49
    assume {:print "$at(2,1469,1518)"} true;
    goto L2;

    // label L0 at .\sources\FirstModule.move:43:36+21
L0:

    // $t7 := 1 at .\sources\FirstModule.move:43:36+21
    assume {:print "$at(2,1496,1517)"} true;
    $t7 := 1;
    assume $IsValid'u64'($t7);

    // trace_abort($t7) at .\sources\FirstModule.move:43:9+49
    assume {:print "$at(2,1469,1518)"} true;
    assume {:print "$track_abort(1,5):", $t7} $t7 == $t7;

    // $t5 := move($t7) at .\sources\FirstModule.move:43:9+49
    $t5 := $t7;

    // goto L4 at .\sources\FirstModule.move:43:9+49
    goto L4;

    // label L2 at .\sources\FirstModule.move:44:69+4
    assume {:print "$at(2,1589,1593)"} true;
L2:

    // $t8 := borrow_global<BasicCoin::Balance<#0>>($t0) on_abort goto L4 with $t5 at .\sources\FirstModule.move:44:32+17
    assume {:print "$at(2,1552,1569)"} true;
    if (!$ResourceExists($cafe_BasicCoin_Balance'#0'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t8 := $Mutation($Global($t0), EmptyVec(), $ResourceValue($cafe_BasicCoin_Balance'#0'_$memory, $t0));
    }
    if ($abort_flag) {
        assume {:print "$at(2,1552,1569)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(1,5):", $t5} $t5 == $t5;
        goto L4;
    }

    // $t9 := borrow_field<BasicCoin::Balance<#0>>.coin($t8) at .\sources\FirstModule.move:44:32+47
    $t9 := $ChildMutation($t8, 0, $coin#$cafe_BasicCoin_Balance'#0'($Dereference($t8)));

    // $t10 := borrow_field<BasicCoin::Coin<#0>>.value($t9) at .\sources\FirstModule.move:44:27+58
    $t10 := $ChildMutation($t9, 0, $value#$cafe_BasicCoin_Coin'#0'($Dereference($t9)));

    // trace_local[balance_ref]($t10) at .\sources\FirstModule.move:44:13+11
    $temp_0'u64' := $Dereference($t10);
    assume {:print "$track_local(1,5,3):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // $t11 := -($t4, $t1) on_abort goto L4 with $t5 at .\sources\FirstModule.move:45:32+1
    assume {:print "$at(2,1639,1640)"} true;
    call $t11 := $Sub($t4, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,1639,1640)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(1,5):", $t5} $t5 == $t5;
        goto L4;
    }

    // write_ref($t10, $t11) at .\sources\FirstModule.move:45:9+31
    $t10 := $UpdateMutation($t10, $t11);

    // write_back[Reference($t9).value (u64)]($t10) at .\sources\FirstModule.move:45:9+31
    $t9 := $UpdateMutation($t9, $Update'$cafe_BasicCoin_Coin'#0''_value($Dereference($t9), $Dereference($t10)));

    // write_back[Reference($t8).coin (BasicCoin::Coin<#0>)]($t9) at .\sources\FirstModule.move:45:9+31
    $t8 := $UpdateMutation($t8, $Update'$cafe_BasicCoin_Balance'#0''_coin($Dereference($t8), $Dereference($t9)));

    // write_back[BasicCoin::Balance<#0>@]($t8) at .\sources\FirstModule.move:45:9+31
    $cafe_BasicCoin_Balance'#0'_$memory := $ResourceUpdate($cafe_BasicCoin_Balance'#0'_$memory, $GlobalLocationAddress($t8),
        $Dereference($t8));

    // $t12 := pack BasicCoin::Coin<#0>($t1) at .\sources\FirstModule.move:46:9+30
    assume {:print "$at(2,1658,1688)"} true;
    $t12 := $cafe_BasicCoin_Coin'#0'($t1);

    // trace_return[0]($t12) at .\sources\FirstModule.move:46:9+30
    assume {:print "$track_return(1,5,0):", $t12} $t12 == $t12;

    // label L3 at .\sources\FirstModule.move:47:5+1
    assume {:print "$at(2,1694,1695)"} true;
L3:

    // return $t12 at .\sources\FirstModule.move:47:5+1
    assume {:print "$at(2,1694,1695)"} true;
    $ret0 := $t12;
    return;

    // label L4 at .\sources\FirstModule.move:47:5+1
L4:

    // abort($t5) at .\sources\FirstModule.move:47:5+1
    assume {:print "$at(2,1694,1695)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun BasicCoin::withdraw [verification] at .\sources\FirstModule.move:41:5+371
procedure {:timeLimit 40} $cafe_BasicCoin_withdraw$verify(_$t0: int, _$t1: int) returns ($ret0: $cafe_BasicCoin_Coin'#0')
{
    // declare local variables
    var $t2: int;
    var $t3: $Mutation (int);
    var $t4: int;
    var $t5: int;
    var $t6: bool;
    var $t7: int;
    var $t8: $Mutation ($cafe_BasicCoin_Balance'#0');
    var $t9: $Mutation ($cafe_BasicCoin_Coin'#0');
    var $t10: $Mutation (int);
    var $t11: int;
    var $t12: $cafe_BasicCoin_Coin'#0';
    var $t0: int;
    var $t1: int;
    var $temp_0'$cafe_BasicCoin_Coin'#0'': $cafe_BasicCoin_Coin'#0';
    var $temp_0'address': int;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at .\sources\FirstModule.move:41:5+1
    assume {:print "$at(2,1324,1325)"} true;
    assume $IsValid'address'($t0);

    // assume WellFormed($t1) at .\sources\FirstModule.move:41:5+1
    assume $IsValid'u64'($t1);

    // assume forall $rsc: ResourceDomain<BasicCoin::Balance<#0>>(): WellFormed($rsc) at .\sources\FirstModule.move:41:5+1
    assume (forall $a_0: int :: {$ResourceValue($cafe_BasicCoin_Balance'#0'_$memory, $a_0)}(var $rsc := $ResourceValue($cafe_BasicCoin_Balance'#0'_$memory, $a_0);
    ($IsValid'$cafe_BasicCoin_Balance'#0''($rsc))));

    // trace_local[addr]($t0) at .\sources\FirstModule.move:41:5+1
    assume {:print "$track_local(1,5,0):", $t0} $t0 == $t0;

    // trace_local[amount]($t1) at .\sources\FirstModule.move:41:5+1
    assume {:print "$track_local(1,5,1):", $t1} $t1 == $t1;

    // $t4 := BasicCoin::balance_of<#0>($t0) on_abort goto L4 with $t5 at .\sources\FirstModule.move:42:23+26
    assume {:print "$at(2,1432,1458)"} true;
    call $t4 := $cafe_BasicCoin_balance_of'#0'($t0);
    if ($abort_flag) {
        assume {:print "$at(2,1432,1458)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(1,5):", $t5} $t5 == $t5;
        goto L4;
    }

    // trace_local[balance]($t4) at .\sources\FirstModule.move:42:13+7
    assume {:print "$track_local(1,5,2):", $t4} $t4 == $t4;

    // $t6 := >=($t4, $t1) at .\sources\FirstModule.move:43:25+2
    assume {:print "$at(2,1485,1487)"} true;
    call $t6 := $Ge($t4, $t1);

    // if ($t6) goto L1 else goto L0 at .\sources\FirstModule.move:43:9+49
    if ($t6) { goto L1; } else { goto L0; }

    // label L1 at .\sources\FirstModule.move:43:9+49
L1:

    // goto L2 at .\sources\FirstModule.move:43:9+49
    assume {:print "$at(2,1469,1518)"} true;
    goto L2;

    // label L0 at .\sources\FirstModule.move:43:36+21
L0:

    // $t7 := 1 at .\sources\FirstModule.move:43:36+21
    assume {:print "$at(2,1496,1517)"} true;
    $t7 := 1;
    assume $IsValid'u64'($t7);

    // trace_abort($t7) at .\sources\FirstModule.move:43:9+49
    assume {:print "$at(2,1469,1518)"} true;
    assume {:print "$track_abort(1,5):", $t7} $t7 == $t7;

    // $t5 := move($t7) at .\sources\FirstModule.move:43:9+49
    $t5 := $t7;

    // goto L4 at .\sources\FirstModule.move:43:9+49
    goto L4;

    // label L2 at .\sources\FirstModule.move:44:69+4
    assume {:print "$at(2,1589,1593)"} true;
L2:

    // $t8 := borrow_global<BasicCoin::Balance<#0>>($t0) on_abort goto L4 with $t5 at .\sources\FirstModule.move:44:32+17
    assume {:print "$at(2,1552,1569)"} true;
    if (!$ResourceExists($cafe_BasicCoin_Balance'#0'_$memory, $t0)) {
        call $ExecFailureAbort();
    } else {
        $t8 := $Mutation($Global($t0), EmptyVec(), $ResourceValue($cafe_BasicCoin_Balance'#0'_$memory, $t0));
    }
    if ($abort_flag) {
        assume {:print "$at(2,1552,1569)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(1,5):", $t5} $t5 == $t5;
        goto L4;
    }

    // $t9 := borrow_field<BasicCoin::Balance<#0>>.coin($t8) at .\sources\FirstModule.move:44:32+47
    $t9 := $ChildMutation($t8, 0, $coin#$cafe_BasicCoin_Balance'#0'($Dereference($t8)));

    // $t10 := borrow_field<BasicCoin::Coin<#0>>.value($t9) at .\sources\FirstModule.move:44:27+58
    $t10 := $ChildMutation($t9, 0, $value#$cafe_BasicCoin_Coin'#0'($Dereference($t9)));

    // trace_local[balance_ref]($t10) at .\sources\FirstModule.move:44:13+11
    $temp_0'u64' := $Dereference($t10);
    assume {:print "$track_local(1,5,3):", $temp_0'u64'} $temp_0'u64' == $temp_0'u64';

    // $t11 := -($t4, $t1) on_abort goto L4 with $t5 at .\sources\FirstModule.move:45:32+1
    assume {:print "$at(2,1639,1640)"} true;
    call $t11 := $Sub($t4, $t1);
    if ($abort_flag) {
        assume {:print "$at(2,1639,1640)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(1,5):", $t5} $t5 == $t5;
        goto L4;
    }

    // write_ref($t10, $t11) at .\sources\FirstModule.move:45:9+31
    $t10 := $UpdateMutation($t10, $t11);

    // write_back[Reference($t9).value (u64)]($t10) at .\sources\FirstModule.move:45:9+31
    $t9 := $UpdateMutation($t9, $Update'$cafe_BasicCoin_Coin'#0''_value($Dereference($t9), $Dereference($t10)));

    // write_back[Reference($t8).coin (BasicCoin::Coin<#0>)]($t9) at .\sources\FirstModule.move:45:9+31
    $t8 := $UpdateMutation($t8, $Update'$cafe_BasicCoin_Balance'#0''_coin($Dereference($t8), $Dereference($t9)));

    // write_back[BasicCoin::Balance<#0>@]($t8) at .\sources\FirstModule.move:45:9+31
    $cafe_BasicCoin_Balance'#0'_$memory := $ResourceUpdate($cafe_BasicCoin_Balance'#0'_$memory, $GlobalLocationAddress($t8),
        $Dereference($t8));

    // $t12 := pack BasicCoin::Coin<#0>($t1) at .\sources\FirstModule.move:46:9+30
    assume {:print "$at(2,1658,1688)"} true;
    $t12 := $cafe_BasicCoin_Coin'#0'($t1);

    // trace_return[0]($t12) at .\sources\FirstModule.move:46:9+30
    assume {:print "$track_return(1,5,0):", $t12} $t12 == $t12;

    // label L3 at .\sources\FirstModule.move:47:5+1
    assume {:print "$at(2,1694,1695)"} true;
L3:

    // return $t12 at .\sources\FirstModule.move:47:5+1
    assume {:print "$at(2,1694,1695)"} true;
    $ret0 := $t12;
    return;

    // label L4 at .\sources\FirstModule.move:47:5+1
L4:

    // abort($t5) at .\sources\FirstModule.move:47:5+1
    assume {:print "$at(2,1694,1695)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// struct MyOddCoin::MyOddCoin at .\sources\MyOddCoin.move:5:5+27
type {:datatype} $cafe_MyOddCoin_MyOddCoin;
function {:constructor} $cafe_MyOddCoin_MyOddCoin($dummy_field: bool): $cafe_MyOddCoin_MyOddCoin;
function {:inline} $Update'$cafe_MyOddCoin_MyOddCoin'_dummy_field(s: $cafe_MyOddCoin_MyOddCoin, x: bool): $cafe_MyOddCoin_MyOddCoin {
    $cafe_MyOddCoin_MyOddCoin(x)
}
function $IsValid'$cafe_MyOddCoin_MyOddCoin'(s: $cafe_MyOddCoin_MyOddCoin): bool {
    $IsValid'bool'($dummy_field#$cafe_MyOddCoin_MyOddCoin(s))
}
function {:inline} $IsEqual'$cafe_MyOddCoin_MyOddCoin'(s1: $cafe_MyOddCoin_MyOddCoin, s2: $cafe_MyOddCoin_MyOddCoin): bool {
    s1 == s2
}

// fun MyOddCoin::transfer [verification] at .\sources\MyOddCoin.move:14:5+187
procedure {:timeLimit 40} $cafe_MyOddCoin_transfer$verify(_$t0: $signer, _$t1: int, _$t2: int) returns ()
{
    // declare local variables
    var $t3: int;
    var $t4: int;
    var $t5: int;
    var $t6: int;
    var $t7: bool;
    var $t8: int;
    var $t9: bool;
    var $t10: $cafe_MyOddCoin_MyOddCoin;
    var $t0: $signer;
    var $t1: int;
    var $t2: int;
    var $temp_0'address': int;
    var $temp_0'signer': $signer;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;
    $t2 := _$t2;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at .\sources\MyOddCoin.move:14:5+1
    assume {:print "$at(3,374,375)"} true;
    assume $IsValid'signer'($t0) && $1_signer_is_txn_signer($t0) && $1_signer_is_txn_signer_addr($addr#$signer($t0));

    // assume WellFormed($t1) at .\sources\MyOddCoin.move:14:5+1
    assume $IsValid'address'($t1);

    // assume WellFormed($t2) at .\sources\MyOddCoin.move:14:5+1
    assume $IsValid'u64'($t2);

    // assume forall $rsc: ResourceDomain<BasicCoin::Balance<MyOddCoin::MyOddCoin>>(): WellFormed($rsc) at .\sources\MyOddCoin.move:14:5+1
    assume (forall $a_0: int :: {$ResourceValue($cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin'_$memory, $a_0)}(var $rsc := $ResourceValue($cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin'_$memory, $a_0);
    ($IsValid'$cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin''($rsc))));

    // trace_local[from]($t0) at .\sources\MyOddCoin.move:14:5+1
    assume {:print "$track_local(2,1,0):", $t0} $t0 == $t0;

    // trace_local[to]($t1) at .\sources\MyOddCoin.move:14:5+1
    assume {:print "$track_local(2,1,1):", $t1} $t1 == $t1;

    // trace_local[amount]($t2) at .\sources\MyOddCoin.move:14:5+1
    assume {:print "$track_local(2,1,2):", $t2} $t2 == $t2;

    // $t3 := 2 at .\sources\MyOddCoin.move:15:26+1
    assume {:print "$at(3,463,464)"} true;
    $t3 := 2;
    assume $IsValid'u64'($t3);

    // $t4 := %($t2, $t3) on_abort goto L4 with $t5 at .\sources\MyOddCoin.move:15:24+1
    call $t4 := $Mod($t2, $t3);
    if ($abort_flag) {
        assume {:print "$at(3,461,462)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,1):", $t5} $t5 == $t5;
        goto L4;
    }

    // $t6 := 1 at .\sources\MyOddCoin.move:15:31+1
    $t6 := 1;
    assume $IsValid'u64'($t6);

    // $t7 := ==($t4, $t6) at .\sources\MyOddCoin.move:15:28+2
    $t7 := $IsEqual'u64'($t4, $t6);

    // if ($t7) goto L1 else goto L0 at .\sources\MyOddCoin.move:15:9+34
    if ($t7) { goto L1; } else { goto L0; }

    // label L1 at .\sources\MyOddCoin.move:15:9+34
L1:

    // goto L2 at .\sources\MyOddCoin.move:15:9+34
    assume {:print "$at(3,446,480)"} true;
    goto L2;

    // label L0 at .\sources\MyOddCoin.move:15:9+34
L0:

    // $t8 := 0 at .\sources\MyOddCoin.move:15:34+8
    assume {:print "$at(3,471,479)"} true;
    $t8 := 0;
    assume $IsValid'u64'($t8);

    // trace_abort($t8) at .\sources\MyOddCoin.move:15:9+34
    assume {:print "$at(3,446,480)"} true;
    assume {:print "$track_abort(2,1):", $t8} $t8 == $t8;

    // $t5 := move($t8) at .\sources\MyOddCoin.move:15:9+34
    $t5 := $t8;

    // goto L4 at .\sources\MyOddCoin.move:15:9+34
    goto L4;

    // label L2 at .\sources\MyOddCoin.move:16:40+4
    assume {:print "$at(3,522,526)"} true;
L2:

    // $t9 := false at .\sources\MyOddCoin.move:16:58+12
    assume {:print "$at(3,540,552)"} true;
    $t9 := false;
    assume $IsValid'bool'($t9);

    // $t10 := pack MyOddCoin::MyOddCoin($t9) at .\sources\MyOddCoin.move:16:58+12
    $t10 := $cafe_MyOddCoin_MyOddCoin($t9);

    // BasicCoin::transfer<MyOddCoin::MyOddCoin>($t0, $t1, $t2, $t10) on_abort goto L4 with $t5 at .\sources\MyOddCoin.move:16:9+62
    call $cafe_BasicCoin_transfer'$cafe_MyOddCoin_MyOddCoin'($t0, $t1, $t2, $t10);
    if ($abort_flag) {
        assume {:print "$at(3,491,553)"} true;
        $t5 := $abort_code;
        assume {:print "$track_abort(2,1):", $t5} $t5 == $t5;
        goto L4;
    }

    // label L3 at .\sources\MyOddCoin.move:17:5+1
    assume {:print "$at(3,560,561)"} true;
L3:

    // return () at .\sources\MyOddCoin.move:17:5+1
    assume {:print "$at(3,560,561)"} true;
    return;

    // label L4 at .\sources\MyOddCoin.move:17:5+1
L4:

    // abort($t5) at .\sources\MyOddCoin.move:17:5+1
    assume {:print "$at(3,560,561)"} true;
    $abort_code := $t5;
    $abort_flag := true;
    return;

}

// fun MyOddCoin::setup_and_mint [verification] at .\sources\MyOddCoin.move:9:5+209
procedure {:timeLimit 40} $cafe_MyOddCoin_setup_and_mint$verify(_$t0: $signer, _$t1: int) returns ()
{
    // declare local variables
    var $t2: int;
    var $t3: int;
    var $t4: bool;
    var $t5: $cafe_MyOddCoin_MyOddCoin;
    var $t0: $signer;
    var $t1: int;
    var $temp_0'signer': $signer;
    var $temp_0'u64': int;
    $t0 := _$t0;
    $t1 := _$t1;

    // verification entrypoint assumptions
    call $InitVerification();

    // bytecode translation starts here
    // assume WellFormed($t0) at .\sources\MyOddCoin.move:9:5+1
    assume {:print "$at(3,157,158)"} true;
    assume $IsValid'signer'($t0) && $1_signer_is_txn_signer($t0) && $1_signer_is_txn_signer_addr($addr#$signer($t0));

    // assume WellFormed($t1) at .\sources\MyOddCoin.move:9:5+1
    assume $IsValid'u64'($t1);

    // assume forall $rsc: ResourceDomain<BasicCoin::Balance<MyOddCoin::MyOddCoin>>(): WellFormed($rsc) at .\sources\MyOddCoin.move:9:5+1
    assume (forall $a_0: int :: {$ResourceValue($cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin'_$memory, $a_0)}(var $rsc := $ResourceValue($cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin'_$memory, $a_0);
    ($IsValid'$cafe_BasicCoin_Balance'$cafe_MyOddCoin_MyOddCoin''($rsc))));

    // trace_local[account]($t0) at .\sources\MyOddCoin.move:9:5+1
    assume {:print "$track_local(2,0,0):", $t0} $t0 == $t0;

    // trace_local[amount]($t1) at .\sources\MyOddCoin.move:9:5+1
    assume {:print "$track_local(2,0,1):", $t1} $t1 == $t1;

    // BasicCoin::publish_balance<MyOddCoin::MyOddCoin>($t0) on_abort goto L2 with $t2 at .\sources\MyOddCoin.move:10:9+46
    assume {:print "$at(3,225,271)"} true;
    call $cafe_BasicCoin_publish_balance'$cafe_MyOddCoin_MyOddCoin'($t0);
    if ($abort_flag) {
        assume {:print "$at(3,225,271)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(2,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t3 := signer::address_of($t0) on_abort goto L2 with $t2 at .\sources\MyOddCoin.move:11:36+27
    assume {:print "$at(3,309,336)"} true;
    call $t3 := $1_signer_address_of($t0);
    if ($abort_flag) {
        assume {:print "$at(3,309,336)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(2,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // $t4 := false at .\sources\MyOddCoin.move:11:73+11
    $t4 := false;
    assume $IsValid'bool'($t4);

    // $t5 := pack MyOddCoin::MyOddCoin($t4) at .\sources\MyOddCoin.move:11:73+11
    $t5 := $cafe_MyOddCoin_MyOddCoin($t4);

    // BasicCoin::mint<MyOddCoin::MyOddCoin>($t3, $t1, $t5) on_abort goto L2 with $t2 at .\sources\MyOddCoin.move:11:9+76
    call $cafe_BasicCoin_mint'$cafe_MyOddCoin_MyOddCoin'($t3, $t1, $t5);
    if ($abort_flag) {
        assume {:print "$at(3,282,358)"} true;
        $t2 := $abort_code;
        assume {:print "$track_abort(2,0):", $t2} $t2 == $t2;
        goto L2;
    }

    // label L1 at .\sources\MyOddCoin.move:12:5+1
    assume {:print "$at(3,365,366)"} true;
L1:

    // return () at .\sources\MyOddCoin.move:12:5+1
    assume {:print "$at(3,365,366)"} true;
    return;

    // label L2 at .\sources\MyOddCoin.move:12:5+1
L2:

    // abort($t2) at .\sources\MyOddCoin.move:12:5+1
    assume {:print "$at(3,365,366)"} true;
    $abort_code := $t2;
    $abort_flag := true;
    return;

}
