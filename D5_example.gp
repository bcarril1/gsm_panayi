read("C:/Users/Ben/Desktop/gsm_panayi/panayi.gp");


gen_D5 = x^5 + (t - 3)*x^4 + (s - t + 3)*x^3+(t^2 - t - 2*s - 1)*x^2 + s*x + t;
gen_D5 = subst(gen_D5,s,5);
gen_D5 = subst(gen_D5,t,w);
p=5;
base_extension = x;
algo_one(gen_D5,local_extension,base_extension,p) =
{
    \\ Running Algorithm 1
    panayi_output = panayi_gen(gen_D5,base_extension,local_extension,p,100,100);

    \\ Cleaning up and putting found polynomials in terms of Q[x]
    raw_list_of_polys = panayi_clean_up(panayi_output[1],subst(panayi_output[2],x,y),subst(panayi_output[3],x,t),gen_D5);
    raw_list_of_polys = apply(z->[eval(z[1]),z[2]],raw_list_of_polys);

    \\ Removing any impossible examples for gsm i.e. reducible poly or prime splits
    filtered_list_of_polys = select(z->polisirreducible(z[1]),raw_list_of_polys);
    filtered_list_of_polys = select(z->#idealprimedec(nfinit(eval(z[1])),p)==1,filtered_list_of_polys );

    \\ Checking if any polynomials left is an gsm
    final_list_of_polys = select(z->panayi(local_extension,z[1],p)[1],filtered_list_of_polys);

    return(final_list_of_polys);
};

D5_list = [x^5 + 15*x^2 + 5,x^5 + 10*x^2 + 5,x^5 + 5*x^4 + 5];

for(l=1,3,print("for ",D5_list[l]);  output = algo_one(gen_D5,D5_list[l],base_extension,p); output = apply(z->[z[1],subst(z[2],y,p)],output);   print(output);print("===================="));