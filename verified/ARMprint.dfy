include "ARMdef.dfy"

function method user_continue_label(): string
{
    "usermode_return_continue"
}

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
method printMode(m:mode)
{
    match m
        case User => print("usr");
        case FIQ => print("fiq");
        case IRQ => print("irq");
        case Supervisor => print("svc");
        case Abort => print("abt");
        case Undefined => print("und");
        case Monitor => print("mon"); //TOOD check this
}

method printReg(r:ARMReg)
{
    match r
        case R0 => print("r0");
        case R1 => print("r1");
        case R2 => print("r2");
        case R3 => print("r3");
        case R4 => print("r4");
        case R5 => print("r5");
        case R6 => print("r6");
        case R7 => print("r7");
        case R8 => print("r8");
        case R9 => print("r9");
        case R10 => print("r10");
        case R11 => print("r11");
        case R12 => print("r12");
        case SP(m) => print("sp_"); printMode(m);
        case LR(m) => print("lr_"); printMode(m);
}

method printShift(s:Shift)
{
    match s
        case LSLShift(amount) => if amount == 0 { 
                                     print("Shifts cannot be 0!"); 
                                 } else { 
                                     print("lsl#"); 
                                     print(amount); 
                                 }
        case LSRShift(amount) => if amount == 0 { 
                                     print("Shifts cannot be 0!"); 
                                 } else { 
                                     print("lsr#"); 
                                     print(amount); 
                                 }
        case RORShift(amount) => if amount == 0 { 
                                     print("Shifts cannot be 0!"); 
                                 } else { 
                                     print("ror#"); 
                                     print(amount); 
                                 }
}

method printOperand(o:operand)
{
    match o
        case OConst(n) => print("#"); print(n);
        case OReg(r) => { printReg(r); }
        case OShift(r, s) => { printReg(r); print(","); printShift(s); }
        case OSReg(r)   => {match r
           case ttbr0   => print("ttbr0");
           case scr     => print("scr");
           case cpsr    => print("cpsr");
           case spsr(m)    => print("spsr");
        }
        case OSP => print("sp");
        case OLR => print("lr");
        case OSymbol(sym) => print "="; print(sym);
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

method printInsFixed(instr:string, ops:string)
{
    print("  ");
    print(instr);
    print(" ");
    print(ops);
    nl();
}

method printMcrMsr(instr:string,op:operand)
{
    print("  ");
    print(instr);
    print(" p15, 0, ");
    printOperand(op);
    print(", c1, c1, 0");
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
        case LSL(dest, src1, src2) => printIns3Op("LSL", dest, src1, src2);
        case LSR(dest, src1, src2) => printIns3Op("LSR", dest, src1, src2);
        case REV(dest, src) => printIns2Op("REV", dest, src);
        case MVN(dest, src) => printIns2Op("MVN", dest, src);
        case LDR(rd, base, ofs) => printInsLdStr("LDR", rd, base, ofs);
        case LDR_global(rd, global, base, ofs) => printInsLdStr("LDR", rd, base, ofs);
        case LDR_reloc(rd, sym) => printIns2Op("LDR", rd, sym);
        case STR(rd, base, ofs) => printInsLdStr("STR", rd, base, ofs);
        case STR_global(rd, global, base, ofs) => printInsLdStr("STR", rd, base, ofs);
        case MOV(dst, src) => printIns2Op("MOV", dst, src);
        case MRS(dst, src) => printIns2Op("MRS", dst, src);
        case MSR(dst, src) => printIns2Op("MSR", dst, src);
        case MRC(dst, src) => if(src.OSReg? && src.sr.scr?) { printMcrMsr("MRC",dst); }
            else { print("MRC for non SCR not impl.");nl(); }
        case MCR(dst,src) => if(dst.OSReg? && dst.sr.scr?) { printMcrMsr("MCR",src); }
            else { print("MCR for non SCR not impl.");nl(); }
        case MOVS_PCLR_TO_USERMODE_AND_CONTINUE =>
            printInsFixed("MOVS", "pc, lr");
            print(user_continue_label()); print(":"); nl();
        // case CPS(mod) => printIns1Op("CPS", mod);
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

method printFunction(symname:string, c:code, n:int) returns(n':int)
{
    nl();
    print(".global "); print(symname); nl();
    print(symname); print(":"); nl();
    n' := printCode(c, n);
}

method printHeader()
{
    print(".arm"); nl();
    print(".section .text"); nl();
}

method printGlobal(symname: string, bytes: int)
{
    print(".lcomm ");
    print(symname);
    print(", ");
    print(bytes);
    nl();
}

function method SymbolName(o:operand): string
    requires o.OSymbol?
{
    match o case OSymbol(name) => name
}

method printBss(gdecls: globaldecls)
    requires ValidGlobalDecls(gdecls)
{
    nl();
    print(".section .bss"); nl();
    print(".align 2"); nl(); // 4-byte alignment
    var syms := (set k | k in gdecls :: k);
    while (|syms| > 0)
        invariant forall s :: s in syms ==> s in gdecls;
    {
        var s :| s in syms;
        printGlobal(SymbolName(s), gdecls[s]);
        syms := syms - {s};
    }
}

method printFooter()
{
}
