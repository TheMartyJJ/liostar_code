module DBStar

open LioStar.Map
open LioStar.Effect.Parameters
open LioStar.Effect

module  G = FStar.Ghost
module L = FStar.List.Tot
module LP = FStar.List.Pure
module G   = FStar.Ghost
module I32 = FStar.Int32
module U32 = FStar.UInt32
module U64 = FStar.UInt64
module U8  = FStar.UInt8
module B   = LowStar.Buffer
module CS  = C.String
module LU = LatticeUsed


type fixedString = U64.t


noeq
type paper = {
  id : (i:U32.t{U32.v i > 0});
  pdf: fixedString;
  review1:option (labeled (fixedString));
}



noextract
let mkBigStack (_:unit) : Ifc (unit)
  (requires fun c0 -> True)
  (ensures fun c0 x c1 -> c0 == c1) = ()

noextract
let startBenchmark (i:U32.t) : Ifc (unit)
  (requires fun c0 -> True)
  (ensures fun c0 x c1 -> c0 == c1) = ()

noextract
let stopBenchmark (_:unit) : Ifc (unit)
  (requires fun c0 -> True)
  (ensures fun c0 x c1 -> c0 == c1) = ()
  
noextract
let mkDB (max:U32.t) : Ifc (unit)
  (requires fun c0 -> True)
  (ensures fun c0 x c1 -> c0 == c1) = ()
  
noextract
let syncDB (_:unit) : Ifc (unit)
  (requires fun c0 -> True)
  (ensures fun c0 x c1 -> c0 == c1) = ()
  


let getMaxId_g () : GTot (n:nat{n > 0}) = 15

noextract
let getMaxId (_:unit) : Ifc (u:U32.t{U32.v u = (getMaxId_g ())})
  (requires fun c0 -> True)
  (ensures fun c0 x c1 -> c0 == c1) = 15ul // just debug for compilation
  
noextract
let getFreeId (_:unit) : Ifc  (u:U32.t{U32.v u > 0 /\ U32.v u <= (getMaxId_g ())})
  (requires fun c0 -> True)
  (ensures fun c0 x c1 -> c0 == c1) = 1ul
  

noextract
let setById (u:U32.t{U32.v u > 0 /\ U32.v u <= (getMaxId_g ())}) (lp:labeled paper) : Ifc (unit)
  (requires fun c0 -> True)
  (ensures fun c0 x c1 -> c0 == c1) = ()
  
noextract
let getById (u:U32.t{U32.v u > 0 /\ U32.v u <= (getMaxId_g ())}) : Ifc (labeled paper)
  (requires fun c0 -> True)
  (ensures fun c0 x c1 -> c0 == c1) = admit (); (label ({id=1ul; pdf=5UL; review1=None}) LU.C)
 

noextract
let loadDB (_:unit) : Ifc (unit)
  (requires fun c0 -> True)
  (ensures fun c0 x c1 -> c0 == c1) = ()
 

noextract
let  print (i:U32.t) : Ifc (unit)
  (requires fun c0 -> True)
  (ensures fun c0 x c1 -> c0 == c1) = ()

noextract
let  printPaper (lp:labeled paper) : Ifc (unit)
  (requires fun c0 -> True)
  (ensures fun c0 x c1 -> c0 == c1) = ()


let rec fetchPapers_h (i:U32.t{U32.v i <= getMaxId_g ()}) : Ifc (list (labeled paper))
  (requires fun c0 -> True)
  (ensures fun c0 x c1 -> c0 == c1)
  (decreases (U32.v i))
 = 
  match i with
  | 0ul -> []
  | _ -> (getById i) :: (fetchPapers_h (U32.sub i 1ul))

let fetchPapers (_:unit) : Ifc (list (labeled paper))
  (requires fun c0 -> True)
  (ensures fun c0 x c1 -> c0 == c1) = 
  (fetchPapers_h (getMaxId ()))


let rec fetchFor_h (i:U32.t{U32.v i <= getMaxId_g ()}) (lbl:labelType) : Ifc (list (labeled paper))
  (requires fun c0 -> True)
  (ensures fun c0 x c1 -> c0 == c1)
  (decreases (U32.v i))
=
  match i with
  | 0ul -> []
  | _ -> let p = getById i in
        if lbl = labelOf p then (
          print i;
          p :: fetchFor_h (U32.sub i 1ul) lbl
        ) else
          fetchFor_h (U32.sub i 1ul) lbl

let save (lp:labeled paper) : Ifc (labeled paper)
  (requires fun c0 -> 
    unlabel_pre lp c0
  )
  (ensures fun c0 x c1 -> 
    unlabel_post lp c0 (valueOf lp) c1)
=
  let j = (unlabel lp).id in
  if (U32.gte (U32.sub j 1ul) (getMaxId ()) ) then
    ()
  else (
    assert(U32.v j - 1 < (getMaxId_g ()));
    setById j lp;
    ()
  );
  lp

let rec filter_user (user:labelType) (l:list (labeled paper))  : Ifc (list (labeled paper))
  (requires fun c0 -> True)
  (ensures fun c0 x c1 -> c0 == c1)
=
  match l with
  | [] -> []
  | hd :: tl -> if canFlow user (labelOf hd) then
                 hd :: (filter_user user tl)
              else
                (filter_user user tl)

let fetchPapers_for (user:labelType) :  Ifc  (list (labeled paper)) 
  (requires fun c -> True)
  (ensures fun c0 x c1 -> c0 == c1)
= 
  let lpapers  = fetchPapers () in
  let lpapers' = filter_user user lpapers in
  lpapers'


let printing (lp:labeled paper) : Ifc (unit)
  (requires fun c -> True)
  (ensures fun c0 x c1 -> c0 == c1)
=
  printPaper lp;
  ()

let incr (lp:labeled paper) (current:labelType) : Ifc (paper)
  (requires fun c -> 
    let lx = (join 
                       (join (current) (labelOf lp))
                       LU.C) in
    unlabel_pre lp c 
    /\ (c.cur `canFlow` current)
    /\ label_pre lx c
  )
  (ensures fun c0 x c1 -> 
    let lx = (join 
                       (join (G.reveal current) (G.reveal (labelOf lp)))
                       LU.C) in
    unlabel_post lp c0 (valueOf lp) c1
    
  )
=
  let p  = unlabel lp in
  let l : labelType = (join LU.C (join current (labelOf lp))) in
  let lv : labeled fixedString = (label 97UL l) in
  let p' = {p with pdf=(U64.add_underspec p.pdf 32UL); review1=Some (lv);} in 
  p'

let incr_C (lp:labeled paper) : Ifc (paper)
  (requires fun c -> 
    let lx = (join 
                       (join LU.C (labelOf lp))
                       LU.C) in
    unlabel_pre lp c 
    /\ (G.reveal c.cur `canFlow` LU.C)
    /\ label_pre lx c
  )
  (ensures fun c0 x c1 -> 
    let lx = (join 
                       (join LU.C (G.reveal (labelOf lp)))
                       LU.C) in
    unlabel_post lp c0 (valueOf lp) c1
    
  ) = 
  incr lp LU.C
  

let add (test:fixedString) (lbl:labelType) : Ifc (unit)
  (requires fun c -> c.cur = LU.Bot)
  (ensures fun c0 x c1 -> c0 == c1)
=
  let j = getFreeId () in
  let i = U32.sub j 1ul in
  
  let l : labelType = lbl in
  let lv = (label ({id=j; pdf=test; review1 = None}) l) in
  let max = (getMaxId ()) in
  assert(U32.v (max) = U32.v i || U32.v (max) > U32.v i);
  assert( (U32.gt i max) = false );
  if (U32.gte i max) then
    ()
  else (
    setById j lv;
    ()
  )

let example (_:unit) : Ifc unit
   (requires fun c -> c.cur = LU.Bot)
   (ensures fun c0 x c1 -> True)//c1.prop == G.hide (fun _ -> True) /\ G.reveal c1.cur = LU.Bot )
   = 
   //loadDB ();
  let l = fetchPapers_for LU.M in
  //let l = map (fun _ -> True) LU.E printing l in 
  //syncDB ();
  //loadDB ();
  //let l = fetchPapers_for LU.M in
  let l = map (fun _ -> True) incr_C l in
  //let l = map (fun _ -> True) LU.E printing l in 
  //syncDB ();
  ()
   
let rec tryAlot (step:U32.t) : Ifc (unit) (decreases %[U32.v step])
(requires fun c -> c.cur = LU.Bot)
  (ensures fun c0 x c1 -> c1 == {c0 with state=c1.state}) =
  let _ = toLabeled (example) () in
  if (step `U32.gt` 0ul) then (
    tryAlot (step `U32.sub` 1ul)
  ) else
    ()

let rec initialize (step:U32.t) : Ifc (unit) (decreases %[U32.v step])
(requires fun c -> c.cur = LU.Bot)
  (ensures fun c0 x c1 -> c1 == c0)
= add 42UL LU.M;
  if U32.gt step 0ul then
    initialize (U32.sub step 1ul)
  else
    ()
  
let main () : Ifc  (I32.t) 
  (requires fun c -> c.cur = LU.Bot)
  (ensures fun c0 x c1 -> True) =
  mkBigStack ();
  let x = 3000ul in
  mkDB x; //10ul
  (initialize (U32.sub x 10ul));
  //syncDB ();
  add 65UL LU.C;add 66UL LU.C;add 67UL LU.M; // id == 3
  add 68UL LU.C;add 69UL LU.C;add 70UL LU.C;
  add 71UL LU.C;add 72UL LU.C;add 73UL LU.C;add 74UL LU.M; // id == 10
  //syncDB ();
  startBenchmark 1000000ul;
  (tryAlot (25000ul)); //75000000ul
  stopBenchmark ();
  //syncDB ();
  0l

[@ (CPrologue "
typedef labeled___DBStar_paper  /*struct {
	int 	label;
	int 	id;
	fixedString 	pdf;
	int 	review_label;
	char 	review_data[STRLEN];
}*/ labeled_paper_t;
extern void setCurrent ( labels l );
extern labels getCurrent( void *unit);
extern void mkDB(uint32_t max);
extern uint32_t getDBsize(void*unit);
extern void loadDB(void *unit);
extern void syncDB(void *unit);
extern uint32_t getMaxId(void*unit);
extern uint32_t getFreeId(void*unit);
extern void setById(uint32_t i, labeled_paper_t p);
extern labeled_paper_t getById(uint32_t i);
extern void print(uint32_t i);
extern void printPaper(labeled_paper_t lp);
extern void mkBigStack (void *unit);
extern void startBenchmark(uint32_t max);
extern void stopBenchmark(void *unit);
")]
let dump () : Ifc (unit)
  (requires fun c -> True)
  (ensures fun c0 x c1 -> True) = ()
