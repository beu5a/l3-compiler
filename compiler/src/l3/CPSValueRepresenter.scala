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
        // n = (rewrite(x) -1 )* (rewrite(y) >> 1) + 1
        // n = t + 1
        // t = a*b
        // a = (rewrite(x) - 1)
        // b = (rewrite(y) >> 1)

        //first without the usage of tempLetP

        //val a = Symbol.fresh("a")
        //val b = Symbol.fresh("b")
        //val t = Symbol.fresh("t")
        //L.LetP(a, CPS.Sub, Seq(rewrite(x),1),
        //  L.LetP(b, CPS.ShiftRight, Seq(rewrite(y),1),
        //    L.LetP(t, CPS.Mul, Seq(a,b),
        //      L.LetP(n, CPS.Add, Seq(t,1), apply(body))
        //    )
        //  )
        //)

        // by using tempLetP

        tempLetP(CPS.ShiftRight, Seq(rewrite(y),1)) { b => 
          tempLetP(CPS.Sub, Seq(rewrite(x),1)) { a => 
            tempLetP(CPS.Mul, Seq(a,b)) { t => 
              L.LetP(n, CPS.Add, Seq(t,1), apply(body))
            }
          }
        }
      case H.LetP(n,L3.IntDiv, Seq(x, y), body) => 
        // n = ((x-1)/(y-1) << 1) + 1
        // n = d + 1
        // d = c << 1
        // c = a / b
        // a = (rewrite(x) - 1) 
        // b = (rewrite(y) - 1)
        tempLetP(CPS.Sub, Seq(rewrite(x),1)) { a => 
          tempLetP(CPS.Sub, Seq(rewrite(y),1)) { b => 
            tempLetP(CPS.Div, Seq(a,b)) { c => 
              tempLetP(CPS.ShiftLeft, Seq(c,1)) { d => 
                L.LetP(n, CPS.Add, Seq(d,1), apply(body))
              }
            }
          }
        }
      case H.LetP(n,L3.IntMod, Seq(x, y), body) =>
        // x mod y = 2( (x-1)/2 mod (y-1)/2 ) + 1
        // n = f + 1
        // f = 2*e
        // e = c mod d
        // c = a/2
        // d = b/2
        // a = (rewrite(x) - 1)
        // b = (rewrite(y) - 1)
        // d can be rewritten as unboxInt(replace(y)) 
        // c can be rewritten as unboxInt(replace(x))
        unboxInt(rewrite(x)) { c =>
          unboxInt(rewrite(y)) { d =>
            tempLetP(CPS.Mod, Seq(c,d)) { e => 
              tempLetP(CPS.ShiftRight, Seq(e,1)) { f => 
                L.LetP(n, CPS.Add, Seq(f,1), apply(body))
              }
            }
          }
        }
          

        // Bitwise operations
        // They are all in the form [a op b] = 2( ([a]-1)/2 op ([b]-1)/2 ) + 1
        // which is rewritten as box(unbox([a]) op unbox([b]))

      case H.LetP(n,L3.IntShiftLeft  ,Seq(x ,y), body) => 
        bitWiseLetP(n,L3.IntShiftLeft, x, y, body)
      case H.LetP(n,L3.IntShiftRight ,Seq(x ,y), body) => 
        bitWiseLetP(n,L3.IntShiftRight, x, y, body)
      case H.LetP(n,L3.IntBitwiseAnd ,Seq(x ,y), body) => 
        bitWiseLetP(n,L3.IntBitwiseAnd, x, y, body)
      case H.LetP(n,L3.IntBitwiseOr  ,Seq(x ,y), body) => 
        bitWiseLetP(n,L3.IntBitwiseOr, x, y, body)
      case H.LetP(n,L3.IntBitwiseXOr ,Seq(x ,y), body) => 
        bitWiseLetP(n,L3.IntBitwiseXOr, x, y, body)

      // Byte operations
      case H.LetP(n,L3.ByteRead  , Seq(),body) => 
        //TODO : simplify
        val t1 = Symbol.fresh("t1")
        val t2 = Symbol.fresh("t2")
        L.LetP(t1, CPS.ByteRead, Seq(),  
          L.LetP(t2, CPS.ShiftLeft, Seq(t1, 1),
            L.LetP(n, CPS.Add, Seq(t2, 1), apply(body))
          )
         )
      case H.LetP(n,L3.ByteWrite , Seq(x), body) => 
        unboxInt(rewrite(x)) { x1 => 
          L.LetP(n, CPS.ByteWrite, Seq(x1), apply(body))
        }


      // Conversions
      case H.LetP(n,L3.IntToChar, Seq(x), body) => ???
      case H.LetP(n,L3.CharToInt, Seq(x), body) => ???

      // Id
      case H.LetP(n,L3.Id, Seq(x), body) => 
        L.LetP(n, CPS.Id, Seq(rewrite(x)), apply(body)) 
 
      case H.Halt(x) => unboxInt(rewrite(x)) { x1 => L.Halt(x1) }
      case _ => throw new Exception("Not implemented yet")

    }
  }


  private def bitWiseLetP(n: L.Name, p: L3Primitive,x: H.Atom,y:H.Atom, body: H.Body): L.Tree = {
        unboxInt(rewrite(x)) { x1 => 
          unboxInt(rewrite(y)) { y1 => 
            tempLetP(l3toCPSbitWise(p), Seq(x1,y1)) { t => 
              boxInt(t,n) { n => 
                apply(body)
              }
            }
          }
        }
  }

  private def l3toCPSbitWise(bitwise: L3Primitive): CPSValuePrimitive = bitwise match {
    case L3.IntShiftLeft => CPS.ShiftLeft
    case L3.IntShiftRight => CPS.ShiftRight
    case L3.IntBitwiseAnd => CPS.And
    case L3.IntBitwiseOr => CPS.Or
    case L3.IntBitwiseXOr => CPS.XOr
    case _ => throw new Exception("Not a bitwise operation")
  }

  private def boxInt(v: L.Name, n: L.Name)(body: L.Name => L.Tree): L.Tree = {
    // n = (v << 1) + 1
    // n = t + 1
    // t = v << 1
    tempLetP(CPS.ShiftLeft, Seq(v,1)) { t => 
      L.LetP(n, CPS.Add, Seq(t,1), body(v))
    }

  }

  private def unboxInt(x: L.Atom)(body: L.Name => L.Tree): L.Tree = {
    tempLetP(CPS.Sub, Seq(x,1)) { x1 => 
      tempLetP(CPS.ShiftRight, Seq(x1,1)) { x2 => 
        body(x2)
      }
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
