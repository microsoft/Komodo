include "x86def.dfy"

method printId(id:id)
{
  match id
  {
    case IdGlobal(g) => print(" !!!NOT IMPLEMENTED!!!");
    case IdLocal(l) => print(" !!!NOT IMPLEMENTED!!!");
    case IdStackSlot(i) => print("dword ptr [esp + "); print(4*i); print("]");
    case IdX86Reg(r) =>
    {
      match r
        case X86Eax => print("eax");
        case X86Ebx => print("ebx");
        case X86Ecx => print("ecx");
        case X86Edx => print("edx");
        case X86Esi => print("esi");
        case X86Edi => print("edi");
        case X86Ebp => print("ebp");
        case X86Eflags => print(" !!!INVALID register!!!");
        case X86Xmm(_) => print(" !!!NOT IMPLEMENTED!!!");
    }
  }
}

method printSmallId(id:id)
{
   if id.IdX86Reg? {
      match id.r  
        case X86Eax => print("al");
        case X86Ebx => print("bl");
        case X86Ecx => print("cl");
        case X86Edx => print("dl");
        case X86Esi => print(" !!!INVALID register!!!");
        case X86Edi => print(" !!!INVALID register!!!");
        case X86Ebp => print(" !!!INVALID register!!!");
        case X86Eflags => print(" !!!INVALID register!!!");
        case X86Xmm(_) => print(" !!!INVALID register!!!");
   } else {
        print(" !!!INVALID small operand!!!  Expected al, bl, cl, or dl."); 
   }
}

method printOprnd(o:oprnd)
{
  match o
  {
    case OConst(n) =>
    {
      if 0 <= n < 0x1_0000_0000 { print(n); }
      else { print(" !!!NOT IMPLEMENTED!!!"); }
    }
    case OVar(x) => printId(x);
    case OHeap(addr, t) => print(" !!!NOT IMPLEMENTED!!!");
  }
}

method printSmallOprnd(o:oprnd)
{
    if o.OVar? { printSmallId(o.x); }
    else { print(" !!!INVALID small operand!!!  Expected al, bl, cl, or dl."); }
}

function method cmpNot(c:ocmp):ocmp
{
  match c
    case OEq => ONe
    case ONe => OEq
    case OLe => OGt
    case OGe => OLt
    case OLt => OGe
    case OGt => OLe
}

method printJcc(c:ocmp)
{
  match c
  {
    case OEq => print("  je ");
    case ONe => print("  jne ");
    case OLe => print("  jbe ");
    case OGe => print("  jae ");
    case OLt => print("  jb ");
    case OGt => print("  ja ");
  }
}

method printIns(ins:ins)
{
  match ins
  {
    case Rand(o) => print("  rdrand "); printOprnd(o); print("\n");
    case Mov32(dst, src) => print ("  mov "); printOprnd(dst); print(", "); printOprnd(src); print("\n");
    case Add32(dst, src) => print ("  add "); printOprnd(dst); print(", "); printOprnd(src); print("\n");
    case Sub32(dst, src) => print ("  sub "); printOprnd(dst); print(", "); printOprnd(src); print("\n");
    case Mul32(src)      => print ("  mul "); printOprnd(src); print("\n");
    case AddCarry(dst, src) => print ("  add "); printOprnd(dst); print(", "); printOprnd(src); print("\n");
    case Xor32(dst, src) => print ("  xor "); printOprnd(dst); print(", "); printOprnd(src); print("\n");
    case And32(dst, src) => print ("  and "); printOprnd(dst); print(", "); printOprnd(src); print("\n");
    case Not32(dst)      => print ("  not "); printOprnd(dst); print("\n");
    case GetCf(dst)      => print ("  setc "); printSmallOprnd(dst); print("\n");

    case Rol32(dst, amount)  =>
        print ("  rol ");
        printOprnd(dst);
        print ", ";
        if amount.OConst? {
            printOprnd(amount);
        }
        else {
            printSmallOprnd(amount);
        }
        print("\n");

    case Ror32(dst, amount) =>
        print ("  ror ");
        printOprnd(dst);
        print ", ";
        if amount.OConst? {
            printOprnd(amount);
        }
        else {
            printSmallOprnd(amount);
        }
        print("\n");

    case Shl32(dst, amount)  =>
        print ("  shl ");
        printOprnd(dst);
        print ", ";
        if amount.OConst? {
            printOprnd(amount);
        }
        else {
            printSmallOprnd(amount);
        }
        print("\n");

    case Shr32(dst, amount) =>
        print ("  shr ");
        printOprnd(dst);
        print ", ";
        if amount.OConst? {
            printSmallOprnd(amount);
        }
        else {
            print "cl";
        }
        print("\n");
  }
}

method printBlock(b:codes, n:int) returns(n':int)
{
  n' := n;
  var i := b;
  while (i.sp_CCons?)
    decreases i
  {
    n' := printCode(i.hd, n');
    i := i.tl;
  }
}

method printCode(c:code, n:int) returns(n':int)
{
  match c
  {
    case Ins(ins) => printIns(ins); n' := n;
    case Block(block) => n' := printBlock(block, n);
    case IfElse(ifb, ift, iff) =>
    {
      var n1 := n;
      var n2 := n + 1;
      print("  cmp "); printOprnd(ifb.o1); print(", "); printOprnd(ifb.o2); print("\n");
      printJcc(cmpNot(ifb.cmp)); print("L"); print(n1); print("\n");
      n' := printCode(ift, n + 2);
      print("  jmp L"); print(n2); print("\n");
      print("L"); print(n1); print(":\n");
      n' := printCode(iff, n');
      print("L"); print(n2); print(":\n");
    }
    case While(b, loop) =>
    {
      var n1 := n;
      var n2 := n + 1;
      print("  jmp L"); print(n2); print("\n");
      print("L"); print(n1); print(":\n");
      n' := printCode(loop, n + 2);
      print("L"); print(n2); print(":\n");
      print("  cmp "); printOprnd(b.o1); print(", "); printOprnd(b.o2); print("\n");
      printJcc(cmpNot(b.cmp)); print("L"); print(n1); print("\n");
    }
  }
}

method printHeader()
{
  print(".686p\n");
  print(".model flat\n");
  print(".code\n");
  print("align 16\n");
  print("@spartanMain@4 proc\n");
}

method printFooter()
{
  print("  ret\n");
  print("@spartanMain@4 endp\n");
  print("end\n");
}

