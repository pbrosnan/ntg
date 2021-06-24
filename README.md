# ntg
## Number Theory Game for [Metamath](http://us.metamath.org)

This is a development of Peano Arithemtic based on Robert Solovay's file [peano.mm](https://github.com/metamath/set.mm/blob/develop/peano.mm), 
which comes included in the [metamath distribution](https://github.com/metamath).
The initial, very naive, goal was to emulate the excellent and inspiring Lean 
[Natural Numbers Game tutorial](https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/) 
written by Kevin Buzzard and Mohammad Pedramfar.  

## Proof that 1 = 0. 

In the course of the development it became clear that Solovay's pa_ax7 needs to
be changed slightly.  
The problem is that, without a disjoint variable condition on z, it is possible to arrive at 
a contradiction.  
This is done at the end of the file in the theorems *zerisone* and *anything*.
The first of these proves that 0=1 and the second proves that any wff is true.

Solovay's pa_ax7 reads as follows:

    pa_ax7 $a |- iff   
                 < x y   
                 exists z = y + x S z $.   

I proposed to change it to: 

     ${      
     $d x z $.    
     $d y z $.    
     pa_ax7 $a |- iff   
                  < x y   
                  exists z = y + x S z $.   
     $}   

And this change has been pushed to the new version of
[peano.mm](https://github.com/metamath/set.mm/blob/develop/peano.mm) in the
[metamath distribution](https://github.com/metamath). 
So, for better or worse, it not longer possible to prove that 1=0 in Peano Arithmetic 
using the version of  
[peano.mm](https://github.com/metamath/set.mm/blob/develop/peano.mm)
distributed by metamath.
For the time being, the version of peano.mm in this ntg git rep still proves 1=0.
I plan to change it soon though. So, if you want to be able to prove anything using
this site, you need to act fast.

## Future goals 

My initial plan was to work on peano.mm until I got a proof of the
irrationality of the square root of 2.  My hope is that this development will
help get people interested
in metamath.  In other words, this is really an educational project.   So I
have tried (and am trying) to include helpful comments about the process I went
through in learning metamath.  For this, the 
[Metamath Book](http://us.metamath.org/downloads/metamath.pdf) was an absolute necessity.
I also used several logic textbooks including Elliott Mendelson's *Introduction to
Mathematical Logic.*   

The real work in metamath is going on in 
set.mm, which can be browsed online in the [Metamath Home Page](http://us.metamath.org).
And there is a "professional grade" development of Peano Arithmetic in 
Mario Carneiro's [mm0](https://github.com/digama0/mm0) using his mm0 system, which is 
closely related to metamath. 


