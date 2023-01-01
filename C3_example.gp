read("C:/Users/Ben/Desktop/gsm_panayi/panayi.gp");


gen_C3 = x^3 - w*x^2 + (w - 3)*x + 1;
base_extension = x^4 + 3*x^3 - 6*x^2 - 18*x - 9;
p=3


algo_one(gen_C3,local_extension,base_extension,p) =
{

    for(prec=1,10,
    \\ Running Algorithm 1
    panayi_output = panayi_gen(gen_C3,base_extension,local_extension,p,700,150+50*prec);

    \\ Cleaning up and putting found polynomials in terms of Q[x]
    raw_list_of_polys = panayi_clean_up(panayi_output[1],subst(panayi_output[2],x,y),t^2-t-1,gen_C3);
    raw_list_of_polys = apply(z->[eval(z[1]),z[2]],raw_list_of_polys);

    \\ Removing any impossible examples for gsm i.e. reducible poly or prime splits
    filtered_list_of_polys = select(z->polisirreducible(z[1]),raw_list_of_polys);
    filtered_list_of_polys = select(z->#idealprimedec(nfinit([eval(z[1]),[p]]),p)==1,filtered_list_of_polys );

    \\ Checking if any polynomials left is an gsm
    for(qq=1,length(filtered_list_of_polys),if(panayi(local_extension,filtered_list_of_polys[qq][1],p)[1]>0,return(filtered_list_of_polys[qq]) ));
    );
};

C3_list =  [x^12 + 12*x^11 - 12*x^10 - 6*x^9 - 9*x^7 + 6*x^6 + 9*x^5 + 9*x^4 + 9*x^3 - 9, x^12 - 6*x^10 - 3*x^9 - 9*x^8 + 9*x^7 - 12*x^6 - 9*x^4 - 9, x^12 - 27*x^11 + 21*x^10 + 39*x^9 - 27*x^8 + 36*x^7 - 3*x^6 + 36*x^5 - 9*x^4 - 9*x^3 + 27*x^2 + 27*x + 18, x^12 - 9*x^11 + 12*x^10 - 9*x^9 + 9*x^8 - 9*x^7 + 12*x^6 + 9*x^5 + 9*x^4 + 9*x^3 - 9, x^12 + 24*x^11 - 39*x^10 - 3*x^9 - 36*x^8 + 27*x^7 + 12*x^6 - 18*x^5 + 18*x^4 + 18*x^3 - 27*x - 36, x^12 - 12*x^11 - 3*x^10 + 9*x^9 + 9*x^8 + 6*x^6 + 9*x^3 - 9, x^12 - 6*x^11 + 6*x^10 + 9*x^9 + 9*x^7 - 3*x^6 + 9*x^5 + 9*x^4 - 9*x^3 - 9, x^12 - 3*x^11 + 6*x^10 - 12*x^9 + 9*x^8 - 3*x^6 - 9*x^3 - 9, x^12 + 3*x^11 - 6*x^10 + 12*x^9 - 9*x^8 - 9*x^7 + 3*x^6 - 9*x^5 + 9*x^4 - 9, x^12 - 30*x^11 - 33*x^10 - 3*x^9 + 9*x^8 - 36*x^7 + 30*x^6 + 27*x^4 + 9*x^3 + 27*x^2 - 27*x + 18, x^12 + 3*x^11 + 12*x^10 - 12*x^9 - 9*x^8 - 12*x^6 + 9*x^5 - 9*x^4 + 9*x^3 - 9, x^12 - 12*x^11 + 6*x^10 + 12*x^9 - 9*x^8 + 3*x^6 + 9*x^5 - 9*x^4 - 9*x^3 - 9, x^12 - 33*x^11 - 21*x^10 - 21*x^9 - 18*x^8 - 9*x^7 - 24*x^6 - 36*x^5 + 18*x^4 - 27*x^3 - 27*x^2 + 27*x + 18, x^12 + 33*x^11 + 12*x^10 - 6*x^9 - 18*x^8 + 9*x^7 + 24*x^6 + 9*x^5 - 36*x^4 - 27*x^2 + 27*x - 36, x^12 + 18*x^11 + 21*x^10 - 27*x^9 - 18*x^8 - 12*x^6 + 27*x^5 - 36*x^4 + 9*x^3 + 27*x^2 - 27*x - 36, x^12 + 3*x^11 + 3*x^10 - 9*x^8 + 9*x^7 + 3*x^6 + 9*x^3 - 9];

for(l=1,16,print("for ",C3_list[l]);  output = algo_one(gen_C3,C3_list[l],base_extension,p); printtex(output[2],C3_list[l],output[1]);print("===================="));