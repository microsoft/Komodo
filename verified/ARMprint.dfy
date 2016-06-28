include "ARMdef.dfy"

method cma()       { print(", "); }
method nl()        { print("\n"); }
method not_impl()  { print("  !!!NOT IMPLEMENTED!!!"); }

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

method printBcc(c:ocmp)
{
	match c
	{
		case OEq => print("BEQ ");
		case ONe => print("BNE ");
		case OLe => print("BLE ");
		case OGe => print("BGE ");
		case OLt => print("BLT ");
		case OGt => print("BGT ");
	}
}

/*
method printId(id:id)
{
    match id
        case LocalVar(slot) => print("[sp, #");print(4*slot);print("]");
        case GlobalVar(n) => not_impl();
}
*/

method printOperand(o:operand)
{
	match o
		case OConst(n) => print("#");print(n);
		case OReg(r) => {match r
			case R(n) => print("r"); print(n);
			case SP(m) => print("this should never happen");
			case LR(m) => print("this should never happen");
		}
        case OSP => print("r13");
        case OLR => print("r14");
        // case OMem(x) => not_impl();
}

method printIns(ins:ins)
{
	match ins
	{
		case ADD(dest, src1, src2) =>
			print("  ADD "); printOperand(dest); cma();
				printOperand(src1); cma();
				printOperand(src2); nl();
        case SUB(dest, src1, src2) =>
			print("  SUB "); printOperand(dest); cma();
				printOperand(src1); cma();
				printOperand(src2); nl();
        case MUL(dest, src1, src2) =>
			print("  MUL "); printOperand(dest); cma();
				printOperand(src1); cma();
				printOperand(src2); nl();
        case UDIV(dest, src1, src2) =>
			print("  UDIV "); printOperand(dest); cma();
				printOperand(src1); cma();
				printOperand(src2); nl();
        case AND(dest, src1, src2) => not_impl();
        case ORR(dest, src1, src2) => not_impl();
        case EOR(dest, src1, src2) => not_impl();
        case ROR(dest, src1, src2) => not_impl();
        case LSL(dest, src1, src2) => not_impl();
        case LSR(dest, src1, src2) => not_impl();
        case MVN(dest, src) => not_impl();
		case LDR(rd, base, ofs) =>
			print("  LDR "); printOperand(rd); cma();
				print("["); printOperand(base); cma();
                printOperand(ofs); print("]"); nl();
		case STR(rd, base, ofs) =>
			print("  STR "); printOperand(rd); cma();
				print("["); printOperand(base); cma();
                printOperand(ofs); print("]"); nl();
		case MOV(dst, src) =>
			print("  MOV "); printOperand(dst); cma();
				printOperand(src); nl();
        case CPS(mod) =>
            print("  CPS "); printOperand(mod); nl();
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
		case Ins(ins) => printIns(ins); n':= n;
    	case Block(block) => n' := printBlock(block, n);
		case IfElse(ifb, ift, iff) => {
			var false_branch := n;
			var end_of_block := n + 1;
			// Do comparison
			print("  cmp "); printOperand(ifb.o1); cma();
				printOperand(ifb.o2); nl();
			// Branch to false branch if cond is false
			printBcc(cmpNot(ifb.cmp)); print("L"); print(false_branch); nl();
			// True branch
      		n' := printCode(ift, n + 2);
      		print("  B L"); print(end_of_block); nl(); 
      		print("L"); print(false_branch); print(":\n");
			// False branch
      		n' := printCode(iff, n');
			// Label end of block
      		print("L"); print(end_of_block); print(":\n");
		}	
    	case While(b, loop) =>
    	{
    	  var n1 := n;
    	  var n2 := n + 1;
    	  print("  B L"); print(n2); print("\n");
    	  print("L"); print(n1); print(":\n");
    	  n' := printCode(loop, n + 2);
    	  print("L"); print(n2); print(":\n");
    	  print("  cmp "); printOperand(b.o1); print(", "); printOperand(b.o2); print("\n");
    	  printBcc(cmpNot(b.cmp)); print("L"); print(n1); print("\n");
    	}
	}
}

method printHeader(){
    print(".arm\n");
    print(".section .text\n");
}

method printFooter(){
}
