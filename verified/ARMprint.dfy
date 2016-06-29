include "ARMdef.dfy"

method nl()
{
    print("\n");
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

method printBcc(c:ocmp)
{
    match c
        case OEq => print("  BEQ ");
        case ONe => print("  BNE ");
        case OLe => print("  BLE ");
        case OGe => print("  BGE ");
        case OLt => print("  BLT ");
        case OGt => print("  BGT ");
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
        case OConst(n) => print("#"); print(n);
        case OReg(r) => {match r
            case R(n) => print("r"); print(n);
            case SP(m) => print("XXX-badreg-bankedSP");
            case LR(m) => print("XXX-badreg-bankedLR");
        }
        case OSP => print("sp");
        case OLR => print("lr");
        // case OMem(x) => not_impl();
}

method printIns3Op(instr:string, dest:operand, src1:operand, src2:operand)
{
    print("  ");
    print(instr);
    print(" ");
    printOperand(dest);
    print(", ");
    printOperand(src1);
    print(", ");
    printOperand(src2);
    nl();
}

method printIns2Op(instr:string, dest:operand, src:operand)
{
    print("  ");
    print(instr);
    print(" ");
    printOperand(dest);
    print(", ");
    printOperand(src);
    nl();
}

method printIns1Op(instr:string, op:operand)
{
    print("  ");
    print(instr);
    print(" ");
    printOperand(op);
    nl();
}

method printInsLdStr(instr:string, dest:operand, base:operand, offset:operand)
{
    print("  ");
    print(instr);
    print(" ");
    printOperand(dest);
    print(", [");
    printOperand(base);
    if (offset != OConst(0)) {
        print(", ");
        printOperand(offset);
    }
    print("]");
    nl();
}

method printIns(ins:ins)
{
    match ins
    {
        case ADD(dest, src1, src2) => printIns3Op("ADD", dest, src1, src2);
        case SUB(dest, src1, src2) => printIns3Op("SUB", dest, src1, src2);
        case MUL(dest, src1, src2) => printIns3Op("MUL", dest, src1, src2);
        case UDIV(dest, src1, src2) => printIns3Op("UDIV", dest, src1, src2);
        case AND(dest, src1, src2) => printIns3Op("AND", dest, src1, src2);
        case ORR(dest, src1, src2) => printIns3Op("ORR", dest, src1, src2);
        case EOR(dest, src1, src2) => printIns3Op("EOR", dest, src1, src2);
        case ROR(dest, src1, src2) => printIns3Op("ROR", dest, src1, src2);
        case LSL(dest, src1, src2) => printIns3Op("LSL", dest, src1, src2);
        case LSR(dest, src1, src2) => printIns3Op("LSR", dest, src1, src2);
        case MVN(dest, src) => printIns2Op("MVN", dest, src);
        case LDR(rd, base, ofs) => printInsLdStr("LDR", rd, base, ofs);
        case STR(rd, base, ofs) => printInsLdStr("STR", rd, base, ofs);
        case MOV(dst, src) => printIns2Op("MOV", dst, src);
        case CPS(mod) => printIns1Op("CPS", mod);
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

method printLabel(n:int)
{
    print("L");
    print(n);
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
            printIns2Op("CMP", ifb.o1, ifb.o2);
            // Branch to false branch if cond is false
            printBcc(cmpNot(ifb.cmp)); printLabel(false_branch); nl();
            // True branch
            n' := printCode(ift, n + 2);
            print("  B "); printLabel(end_of_block); nl();
            printLabel(false_branch); print(":"); nl();
            // False branch
            n' := printCode(iff, n');
            // Label end of block
            printLabel(end_of_block); print(":"); nl();
        }   
        case While(b, loop) =>
        {
          var n1 := n;
          var n2 := n + 1;
          print("  B "); printLabel(n2); nl();
          printLabel(n1); print(":"); nl();
          n' := printCode(loop, n + 2);
          printLabel(n2); print(":"); nl();
          printIns2Op("CMP", b.o1, b.o2);
          printBcc(cmpNot(b.cmp)); printLabel(n1); nl();
        }
    }
}

method printHeader(symname:string)
{
    print(".arm"); nl();
    print(".section .text"); nl();
    print(".global "); print(symname); nl();
    print(symname); print(":"); nl();
}

method printFooter()
{
}
