package l3

import FlatCPSTreeModule as F

object CPSHoister extends (F.Tree => F.LetF) {
  def apply(tree: F.Tree): F.LetF =
    tree match
      case F.LetF(funs, body) => {
        val F.LetF(funs1, body1) = apply(body)
        def funToFun(f: F.Fun): (F.Fun,Seq[F.Fun]) = {
          val F.LetF(fsi, ei) = apply(f.body)
          (F.Fun(f.name, f.retC, f.args, ei), fsi)
        }
        val (f1, f2) = funs.map(funToFun).unzip 
        F.LetF(f1 ++ f2.flatten ++ funs1, body1) 
      }

      case F.LetC(cnts, body) => {
        val F.LetF(fs, e) = apply(body)
        def cntToCnt(c: F.Cnt): (F.Cnt,Seq[F.Fun]) = {
          val F.LetF(fsii, ei) = apply(c.body)
          (F.Cnt(c.name, c.args, ei), fsii)
        }
        val (cntsi, fsi) = cnts.map(cntToCnt).unzip
        F.LetF(fsi.flatten ++ fs, F.LetC(cntsi,e))
      }

      case F.LetP(name, prim, args, body) =>{
        val F.LetF(funs1, body1) = apply(body)
        F.LetF(funs1,F.LetP(name,prim,args,body1))
      }

      case reste: F.Body => 
        F.LetF(Seq(),reste)
      //case F.AppC(cnt, args) => 
      //  F.LetF(Seq(), F.AppC(cnt, args))
      //case F.AppF(fun, retC, args) => 
      //  F.LetF(Seq(), F.AppF(fun, retC, args))
      //case F.If(cond, args, thenC, elseC) => 
      //  F.LetF(Seq(), F.If(cond, args, thenC, elseC))
      //case F.Halt(arg) => 
      //  F.LetF(Seq(), F.Halt(arg))
    }