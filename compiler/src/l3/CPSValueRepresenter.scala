package l3

import l3.{HighCPSTreeModule as H}
import l3.{LowCPSTreeModule as L}

import l3.{L3Primitive as L3}
import l3.{CPSValuePrimitive as CPS}
import l3.{CPSTestPrimitive as CPST}
import CL3Literal._


object CPSValueRepresenter extends (H.Tree => L.Tree) {
  def apply(tree: H.Tree): L.Tree = {
    transform(tree) // transform is for trees , rewrite is for atoms
  }

  
  private def transform(tree: H.Tree): L.Tree = {
    tree match {  
      // Continuations
      case H.LetC(cs,e) => 
        L.LetC(cs.map(c => L.Cnt(c.name, c.args, transform(c.body))), transform(e))
      case H.AppC(c, as) => 
        L.AppC(c, as.map(rewrite))
      
      // Functions, wrong transformation
      case H.LetF(fs,e) => 
        L.LetF(fs.map(f => L.Fun(f.name, f.retC, f.args, transform(f.body))), transform(e))
      case H.AppF(f,retC,as) =>
        L.AppF(rewrite(f), retC, as.map(rewrite))
      
      // Integers
      case H.LetP(n,L3.IntAdd, Seq(x, y), body) =>  
        // use xor for substraction ? why not use sub
        tempLetP(CPS.XOr, Seq(rewrite(x), 1)) { x1 => 
          L.LetP(n, CPS.Add, Seq(x1,rewrite(y)), apply(body))
        }
      case H.LetP(n,L3.IntSub, Seq(x, y), body) =>
        // use or for addition
        tempLetP(CPS.Or, Seq(rewrite(x), 1)) { x1 => 
          L.LetP(n, CPS.Sub, Seq(x1,rewrite(y)), apply(body))
        }
      case H.LetP(n,L3.IntMul, Seq(x, y), body) => 
        ???
      case _ => ???




    }
  }

  private def rewrite(a:H.Atom):L.Atom = {
    // Atom = Name | Literal
    a match {
      // case n: H.Name => n
      case n: H.Name => n

      // case l: H.Literal => l
      case IntLit(v) => (v.toInt  <<  1) | 1
      case CharLit(c) => (c.toInt << 3) | 6  //0b110
      case BooleanLit(true) =>  26 //0b11010
      case BooleanLit(false) => 10 //0b01011
      case UnitLit => 2 //0b10
    }
  }

  private def tempLetP(p: L.ValuePrimitive, args: Seq[L.Atom])(body: L.Name => L.Tree): L.Tree = {
    val tempSym = Symbol.fresh("t")
    L.LetP(tempSym, p, args, body(tempSym))
  }

}
