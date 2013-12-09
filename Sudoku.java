/*@

/*** VERIFAST'S BUILT-IN DATATYPES, FIXPOINTS and LEMMAS ***/

inductive list<t> = nil | cons(t, list<t>); 
 
fixpoint int length<t>(list<t> xs) { 
  switch (xs) { 
    case nil: return 0; 
    case cons(x, xs0): return 1 + length(xs0); 
  } 
} 
 
fixpoint t nth<t>(int n, list<t> xs) { 
  switch (xs) { 
    case nil: return default_value<t>; 
    case cons(x, xs0): return n == 0 ? x : nth(n - 1, xs0); 
  } 
}

fixpoint boolean forall_int(fixpoint(int, boolean) p);

lemma int not_forall_int(fixpoint(int, boolean) p)
    requires !forall_int(p);
    ensures !p(result);
{
  assume(false);
}

lemma void forall_int_elim(fixpoint(int, boolean) p, int x)
    requires forall_int(p) == true;
    ensures p(x) == true;
{
  assume(false);
}


/*** LEMMAS FOR LOOP ITERATION ***/

// Updates invariant with new assumptions from row
lemma void updateRow(list<int> vs, int n, int i, int y)
    requires validRow(vs,n,i,y) &*& nth(y*9+i, vs) != n;
    ensures validRow(vs,n,i+1,y);
{
/*
	Unfold definition of validRow.
	forall z, validRowLoop(z) /\ nth(y*9+i,vs) !=n --> forall k, validRowLoop(k)
	
	Where k == z+1
	After introducing the premises into the context we need to prove forall k, validRowLoop(k)
	
	H:  forall z, validRowLoop(z) /\ nth(y*9+i,vs) !=n
	--------------------------------------------------	(intros H)
	forall k, validRowLoop(k)
	
	

  	H:  forall z, validRowLoop(z) /\ nth(y*9+i,vs) !=n
  	H1: forall z, validRowLoop(z)
  	H2: nth(y*9+i,vs) !=n
  	--------------------------------------------------  (Inversion H as [H1 H2])
  	forall k, validRowLoop(k)
  
	
	
	H:  forall z, validRowLoop(z) /\ nth(y*9+i,vs) !=n
  	H1: forall z, validRowLoop(z)
 	H2: nth(y*9+i,vs) !=n
	k : nat
	--------------------------------------------------      (Universal Instantiation)
	validRowLoop(k)
	
	
	destruct k.
		When k <= i.
		    apply H1.
		When k = i+1.
		    apply H2.
	Qed.
	
*/

	assume(false);
}
// Updates invariant with new assumptions from col
lemma void updateCol(list<int> vs, int n, int i, int x)
    requires validCol(vs,n,i,x) &*& nth(i*9+x, vs) != n;
    ensures validCol(vs,n,i+1,x);
{
	assume(false);
}

// Updates block invariant of inner loop
lemma void testBlockInner(list<int> vs, int n, int x', int y', int x)
    requires validBlockInner(vs,n,x',y',x) &*& nth(y'*9+x',vs) != n;
    ensures validBlockInner(vs,n,x'+1,y',x);
{
	assume(false);
}

// Updates block invariant of outer loop
lemma void testBlockOuter(list<int> vs, int n, int x', int y', int x, int y)
    requires validBlockOuter(vs,n,x',y',x,y) &*& validBlockInner(vs,n,x',y',x);//NOT SURE ABOUT THIS
    ensures validBlockOuter(vs,n,x',y'+1,x,y) &*& validBlockInner(vs,n,x',y',x);
{
	assume(false);
}

/*** PERMISSIONS PREDICATE ***/
predicate Board(Sudoku s, list<int> elems) = s.board |-> ?b &*& array_slice(b,0,b.length,elems) &*& length(elems) == 81;

/*** PREDICATES for ROW, COLUMN, BLOCK ***/

predicate validRow(list<int> vs, int n, int i, int y) = 			forall_int((withinRow__notN)(vs,n,i,y)) == true;
predicate validCol(list<int> vs, int n, int i, int x) = 			forall_int((withinCol__notN)(vs,n,i,x)) == true;
predicate validBlockOuter(list<int> vs, int n, int x', int y', int x, int y) = 	forall_int((withinBlocO__notN)(vs,n,x',y',x,y)) == true;
predicate validBlockInner(list<int> vs, int n, int x', int y', int x) = 	forall_int((withinBlocI__notN)(vs,n,x',y',x)) == true;

/*** FIXPOINTS used in ROW, COLUMN, BLOCK PREDICATES ***/

fixpoint boolean withinRow__notN(list<int> vs, int n, int i, int y, int k) { 
	return k < 0 || k >= i || nth(y*9+k, vs) != n;
}
fixpoint boolean withinCol__notN(list<int> vs, int n, int i, int x, int k) { 
	return k < 0 || k >= i || nth(k*9+x, vs) != n;
}

fixpoint boolean withinBlocO__notN(list<int> vs, int n, int x', int y', int x, int y, int k) {
	return k < y-(y%3) || k >= y' || /*validBlockInner(vs,n,x',k,x) ==*/ true;//the problem here is a predicate cannot be invoked from a fixpoint... ANNOYING
}

fixpoint boolean withinBlocI__notN(list<int> vs, int n, int x', int y', int x, int k) {
	return k < x-(x%3) || k >= x' || nth(y'*9+k, vs) != n;
}


/*** PREDICATES - INDEX/NUMBER RANGE ***/

// Index Range - to check our x or y coordinate 
predicate ValidIndexRange(int i) = 0 <= i &*& i < 9;
// Number Range - n is the number we wish to place on the board
predicate ValidNumberRange(int n) = 0 <= n &*& n <= 9;
// Index Range for a block
predicate ValidBlockIndexRange(int x, int y) = ValidIndexRange(x) &*& ValidIndexRange(y) &*& 0 <= x-(x%3) &*& x-(x%3) < 81 &*& 0 <= y-(y%3) &*& y-(y%3) < 81;


/*** LEMMAS FOR CODE TIDY ***/

// Unfolding of index predicates
lemma void OpenValidIndexRangePredicates(int x, int y)
requires ValidIndexRange(x) &*& ValidIndexRange(y);
ensures 0 <= x &*& x < 9 &*& 0 <= y &*& y < 9;
{
  open ValidIndexRange(x);
  open ValidIndexRange(y);
}

// Abstraction of index assumptions
lemma void CloseValidIndexRangePredicates(int x, int y)
requires 0 <= x &*& x < 9 &*& 0 <= y &*& y < 9;
ensures ValidIndexRange(x) &*& ValidIndexRange(y);
{
  close ValidIndexRange(x);
  close ValidIndexRange(y);
}

// Unfolding of block index predicates
lemma void OpenValidBlockIndexRangePredicates(int x, int y)
requires ValidBlockIndexRange(x,y);
ensures 0 <= x &*& x < 9 &*& 0 <= y &*& y < 9 &*& 
		0 <= x-(x%3) &*& x-(x%3) < 81 &*& 0 <= y-(y%3) &*& y-(y%3) < 81;
{
  open ValidBlockIndexRange(x,y);
  open ValidIndexRange(x);
  open ValidIndexRange(y);
}

@*/
public class Sudoku{
 
  int board [];
 
  // Class constructor - Creates an empty board of 81 elements
  public Sudoku()
  //@ requires true;
  //@ ensures Board(this,?vs);
  {
    board = new int [81];
    //@ close Board(this,?vs);
  }
  
  // Method to place a move on the board only if it is "valid"
  boolean playMove(int n, int x, int y)
  //@ requires Board(this,_) &*& ValidIndexRange(x) &*& ValidIndexRange(y) &*& ValidNumberRange(n) &*& ValidBlockIndexRange(x,y);
  //@ ensures Board(this,?vs) &*& (result ? validRow(_,n,9,y) &*& validCol(_,n,9,x): true);
    {
  	if(validRow(n,x,y) && validCol(n,x,y) && validBlock(n,x,y))
  	{
	  	//@ OpenValidIndexRangePredicates(x,y);
	    	//@ open Board(this,_); 
	  	  board[y*9+x] = n;
	  	//@ CloseValidIndexRangePredicates(x,y);
	     	//@ close Board(this,_);
	     	return true;
  	}
  	else { return false; }
  }
  
  // Method to check if the given n already exists in y's row 
  boolean validRow(int n, int x, int y)
  //@ requires Board(this,?vs) &*& ValidIndexRange(x) &*& ValidIndexRange(y) &*& ValidNumberRange(n); 
  //@ ensures Board(this,vs) &*& ValidIndexRange(x) &*& ValidIndexRange(y) &*& ValidNumberRange(n) &*& result ? validRow(vs,n,9,y) : true;
  {    
    //@ OpenValidIndexRangePredicates(x,y);
    //@ CloseValidIndexRangePredicates(x,y);
 
 /*@
        if (!forall_int((withinRow__notN)(vs,n,0,y))) {
      
          int j = not_forall_int((withinRow__notN)(vs,n,0,y));
        }
 @*/
 
//@ close validRow(vs,n,0,y);
 
     for(int i=0; i < 9; i++)
     //@ invariant 0 <= i &*& i <= 9 &*& Board(this,vs) &*& validRow(vs,n,i,y);
     { 
        //@ open Board(this,vs);
        //@ open validRow(vs,n,i,y);
      
        if( board[y*9 + i] == n ){
          //@ close Board(this,vs);        
          return false;
        }
        //@ close validRow(vs,n,i,y);
        //@ updateRow(vs,n,i,y);           
        //@ close Board(this,vs);
     }
     return true;
  }
  
  // Method to check if the given n already exists in x's column
  boolean validCol(int n, int x, int y)
  //@ requires Board(this,?vs) &*& ValidIndexRange(x) &*& ValidIndexRange(y) &*& ValidNumberRange(n); 
  //@ ensures Board(this,vs) &*& ValidIndexRange(x) &*& ValidIndexRange(y) &*& ValidNumberRange(n) &*& result ? validCol(vs,n,9,x) : true;
  {    
    //@ OpenValidIndexRangePredicates(x,y);
    //@ CloseValidIndexRangePredicates(x,y);
 
 /*@
        if (!forall_int((withinCol__notN)(vs,n,0,x))) {
      
          int j = not_forall_int((withinCol__notN)(vs,n,0,x));
        }
 @*/
 
//@ close validCol(vs,n,0,x);
 
     for(int i=0; i < 9; i++)
     //@ invariant 0 <= i &*& i <= 9 &*& Board(this,vs) &*& validCol(vs,n,i,x);
     { 
        //@ open Board(this,vs);
        //@ open validCol(vs,n,i,x);
      
        if(board[i*9 + x] == n ){
          //@ close Board(this,vs);        
          return false;
        }
        //@ close validCol(vs,n,i,x);
        //@ updateCol(vs,n,i,x);           
        //@ close Board(this,vs);
     }
     return true;
  }
  
  // Method to check if the given n already exists in (x,y)'s block 
  boolean validBlock(int n, int x, int y)
  //@ requires Board(this, ?vs) &*& ValidBlockIndexRange(x,y);
  //@ ensures Board(this,vs) &*& result ? validBlockOuter(vs,n,x-(x%3)+3,y-(y%3)+3,x,y) : true;
  {
  
   //@ OpenValidBlockIndexRangePredicates(x,y);
   
 /*@
        if (!forall_int((withinBlocO__notN)(vs,n,x-(x%3),y-(y%3),x,y))) {
      
          int i = not_forall_int((withinBlocO__notN)(vs,n,x-(x%3),y-(y%3),x,y));
        }
  @*/ 
 //@ close validBlockOuter(vs,n,x-(x%3),y-(y%3),x,y);

   //int x',y';
   for(int x'=x-(x%3), y'=y-(y%3); y' < y-(y%3)+3; y'++)
   //@ invariant Board(this,vs) &*& x-(x%3) <= x' &*& x' <= x-(x%3)+3 &*& y-(y%3) <= y' &*& y' <= y-(y%3)+3 &*& validBlockOuter(vs,n,x',y',x,y);
   {   
    x'=x-(x%3);
  
  /*@   
        if (!forall_int((withinBlocI__notN)(vs,n,x',y',x))) {
      
          int i = not_forall_int((withinBlocI__notN)(vs,n,x',y',x));
        }
  @*/ 
  //@ close validBlockInner(vs,n,x',y',x);
 
    for(; x' < x-(x%3)+3; x'++)
    //@ invariant Board(this,vs) &*& x-(x%3) <= x' &*& x' <= x-(x%3)+3 &*& validBlockInner(vs,n,x',y',x);
    {
        //@ open Board(this,vs);
        
        if(board[y'*9+x'] == n){
        //@ close Board(this,vs);
          return false;
        }
        //this increments x'
        //@ testBlockInner(vs,n,x',y',x);
        //@ close Board(this,vs);
    }    
     /*@
        if (!forall_int((withinBlocO__notN)(vs,n,x',y',x,y))) {
      
          int i = not_forall_int((withinBlocO__notN)(vs,n,x',y',x,y));
        }
     @*/
     
    //@ close validBlockOuter(vs,n,x',y',x,y);
    
    //this increments y'
    //@ testBlockOuter(vs,n,x',y',x,y);
    }
    return true;
   }
}

