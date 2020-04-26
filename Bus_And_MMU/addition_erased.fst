(fun x y ->
    let _ =
      let _ =
        let _ = Core.LioStar.unlabel (LioStar.Meta.erase Prims.int x (Bus.Lattice.Bot)) in
        let _ = Core.LioStar.unlabel (LioStar.Meta.erase Prims.int y (Bus.Lattice.Bot)) in
        _ + _
      in
      let _ =
        let _ = Core.LioStar.get () in
        LioStar.Meta.erase Prims.int (Core.LioStar.labelUNSAFE _ _) (Bus.Lattice.Bot)
      in
      LioStar.Meta.erase Prims.int _ (Bus.Lattice.Bot)
    in
    LioStar.Meta.erase Prims.int _ (Bus.Lattice.Bot)) ==
Prims.magic ()