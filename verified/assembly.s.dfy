newtype{:nativeType "ulong"} uint32 = i:int | 0 <= i < 0x1_0000_0000

//-/////////////////////////////////////////////
//-  Abstract definitions of 32-bit operations
//-  that we may want to talk about in specs
//-/////////////////////////////////////////////

 
function method{:axiom} UndefinedBit(index:uint32, val:uint32):bool
function method{:axiom} IntBit_spec(index:uint32, val:uint32):bool
//{
//    var bits := BEWordToBitSeq(val);
//    if 0 <= index < |bits| then bits[index] == 1
//    else UndefinedBit(index, val)
//}
function method{:axiom} BitwiseAnd(x:uint32, y:uint32) : uint32
    ensures forall i {:trigger IntBit_spec(i, BitwiseAnd(x, y))} :: 0 <= i < 32 ==> IntBit_spec(i, BitwiseAnd(x, y)) == (IntBit_spec(i, x) && IntBit_spec(i, y));

function method{:axiom} BitwiseOr(x:uint32, y:uint32):uint32
    ensures forall i {:trigger IntBit_spec(i, BitwiseOr(x, y))} :: 0 <= i < 32 ==> IntBit_spec(i, BitwiseOr(x, y)) == (IntBit_spec(i, x) || IntBit_spec(i, y));

function method{:axiom} BitwiseNot(x:uint32) : uint32
    ensures forall i {:trigger IntBit_spec(i, BitwiseNot(x))} :: 0 <= i < 32 ==> IntBit_spec(i, BitwiseNot(x)) == !IntBit_spec(i, x);

function method{:axiom} BitwiseXor(x:uint32, y:uint32) : uint32
    ensures forall i {:trigger IntBit_spec(i, BitwiseXor(x, y))} :: 0 <= i < 32 ==> IntBit_spec(i, BitwiseXor(x, y)) == (IntBit_spec(i, x) != IntBit_spec(i, y));

function method{:axiom} RotateRight(x:uint32, amount:uint32) : uint32
    requires 0 <= amount < 32;
    ensures forall i {:trigger IntBit_spec(i, RotateRight(x, amount))} :: 0 <= i < amount ==>  IntBit_spec(i, RotateRight(x, amount)) == IntBit_spec((32 - amount)+i, x);
    ensures forall i {:trigger IntBit_spec(i, RotateRight(x, amount))} :: amount <= i < 32 ==> IntBit_spec(i, RotateRight(x, amount)) == IntBit_spec(i - amount, x);

function method{:axiom} RotateLeft(x:uint32, amount:uint32):uint32
    requires 0 <= amount < 32;
    ensures forall i {:trigger IntBit_spec(i, RotateLeft(x, amount))} :: 0 <= i < 32 - amount ==> IntBit_spec(i, RotateLeft(x, amount)) == IntBit_spec(i + amount, x);
    ensures forall i {:trigger IntBit_spec(i, RotateLeft(x, amount))} :: 32 - amount <= i < 32 ==> IntBit_spec(i, RotateLeft(x, amount)) == IntBit_spec(i - (32 - amount), x);         

function method{:axiom} RightShift(x:uint32, amount:uint32) : uint32
    requires 0 <= amount < 32;
    ensures forall i {:trigger IntBit_spec(i, RightShift(x, amount))} :: 0 <= i < amount ==> IntBit_spec(i, RightShift(x, amount)) == false;            
    ensures forall i {:trigger IntBit_spec(i, RightShift(x, amount))} :: amount <= i < 32 ==> IntBit_spec(i, RightShift(x, amount)) == IntBit_spec(i - amount, x);            

function method{:axiom} LeftShift(x:uint32, amount:uint32) : uint32
    requires 0 <= amount < 32;
    ensures forall i {:trigger IntBit_spec(i, LeftShift(x, amount))} :: 32 - amount <= i < 32 ==>  IntBit_spec(i, LeftShift(x, amount)) == false;
    ensures forall i {:trigger IntBit_spec(i, LeftShift(x, amount))} :: 0 <= i < 32 - amount ==> IntBit_spec(i, LeftShift(x, amount)) == IntBit_spec(i + amount, x);

function method{:axiom} BitwiseAdd32(x:uint32, y:uint32):uint32
    ensures BitwiseAdd32(x, y) == uint32((int(x) + int(y)) % 0x100000000);

function method{:axiom} BitwiseSub32(x:uint32, y:uint32):uint32
    //ensures Sub32(x, y) == (int(x) - int(y)) % 0x100000000;

function method{:axiom} BitwiseMul32(x:uint32, y:uint32):uint32
    //ensures Mul32(x, y) == (int(x) * int(y)) % 0x100000000;

function method{:axiom} BitwiseDiv32(x:uint32, y:uint32):uint32
    requires y != 0;
    //ensures Div32(x, y) == (int(x) / int(y)) % 0x100000000;

function method{:axiom} BitwiseMod32(x:uint32, y:uint32):uint32
    requires y != 0;
    //ensures Mod32(x, y) == (int(x) % int(y)) % 0x100000000;

lemma {:axiom} lemma_BitwiseCommutative(x:uint32, y:uint32)
    ensures BitwiseAnd(x, y) == BitwiseAnd(y, x);
    ensures BitwiseXor(x, y) == BitwiseXor(y, x);
    ensures BitwiseOr(x, y) == BitwiseOr(y, x);


