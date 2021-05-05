//zeller.cpp
#include "mlisp.h"
double day__of__week();
double zeller(double d, double m, double y, double c);
double neg__to__pos(double d);
double birthday(double dw);
extern double dd;
extern double mm;
extern double yyyy;
//...
//(define (neg-to-pos d)
// (cond((< d 0)(+ d 7))
//      (#t d)
// )
//)
double neg__to__pos(double d){
 return (d < 0. ? d + 7.
         : true ? d
         : _infinity
        );
}
double birthday(double dw){
 display("Your were born on ");
//...
 return  yyyy;
}
double dd = 31;
//...
int main(){
 display(birthday (day__of__week()));
 newline();

 std::cin.get();
 return 0;
}
