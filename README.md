# ntg
Number Theory Game for [Metamath](us.metamath.org)

This is a development of Peano Arithemtic based on Robert Solovay's file peano.mm, 
which comes included in the [metamath-exe distribution](https://github.com/metamath/metamath-exe).
The initial, very naive, goal was to emulate the excellent and inspiring Lean 
[Natural Numbers Game tutorial](https://www.ma.imperial.ac.uk/~buzzard/xena/natural_number_game/) 
written by Kevin Buzzard and Mohammad Pedramfar.  

In the course of the development it became clear that Solovay's pa_ax7 needs to
be changed slightly.  
The problem is that, without a distinct variable condition on z, it is possible to arrive at 
a contradiction.  
This is done at the end of the file in the theorems *zerisone* and *anything*.
The first of these proves that 0=1 and the second proves that any wff is true.

Solovay's pa_ax7 reads as follows:

    pa_ax7 $a |- iff   
                 < x y   
                 exists z = y + x S z $.   

I propose to change it to: 

     ${      
     $d x z $.    
     $d y z $.    
     pa_ax7 $a |- iff   
                  < x y   
                  exists z = y + x S z $.   
     $}   

