package l3

import FlatCPSTreeModule as F
import LowCPSTreeModule as L

object CPSHoister extends (L.Tree => F.LetF) {
  def apply(tree: L.Tree): F.LetF =
    tree match
      case L.LetF(funs, body) => {
        val F.LetF(funs1, body1) = apply(body)
        def funToFun(f: L.Fun): (F.Fun,Seq[F.Fun]) = {
          val F.LetF(fsi, ei) = apply(f.body)
          (F.Fun(f.name, f.retC, f.args, ei), fsi)
        }
        val (f1, f2) = funs.map(funToFun).unzip 
        F.LetF(f1 ++ f2.flatten ++ funs1, body1) 
      }

      case L.LetC(cnts, body) => {
        val F.LetF(fs, e) = apply(body)
        def cntToCnt(c: L.Cnt): (F.Cnt,Seq[F.Fun]) = {
          val F.LetF(fsii, ei) = apply(c.body)
          (F.Cnt(c.name, c.args, ei), fsii)
        }
        val (cntsi, fsi) = cnts.map(cntToCnt).unzip
        F.LetF(fsi.flatten ++ fs, F.LetC(cntsi,e))
      }

      case L.LetP(name, prim, args, body) =>{
        val F.LetF(funs1, body1) = apply(body)
        F.LetF(funs1,F.LetP(name,prim,args,body1))
      }

      //pas sur de ça
      case reste => 
        F.LetF(Seq(),reste.asInstanceOf[F.Body])
    }