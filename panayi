panayi_gen(gen_pol,base_extension,local_extension,p,option) =
{

	\\ gen_pol: a generic/parametric polynomial in x and w is the parameter (thus only one parameter allowed in this implementation)
	\\ base_extension: a Galois splitting model of the base extension in terms of x (assuming that base_extension contains the maximal unramified extension of local_extension)
	\\ local_extension: to Q_p extension we are trying to find a Galois splitting model
	\\ Implementation 1: Uses the command polrootsff to find the needed roots modulo the prime ideal above p, 
	\\ but method needs polynomials defining unramified/totally ramified parts of the extension. So if g is a polynomial and 
	\\ not a vector, then the implementation will find polynomials defined unramified/totally ramified parts of the extension and 
	\\ uses the "option" value to determine on how to find them. 
	\\ When local_extension is a polynomial and when option is 0 or omitted, then uses a lexiographical ordering to find the polynomial defining unramified part of the extension K  	
	\\ When local_extension is a polynomial and when option is 1, then the command ffinit to define unramified part of the extension K  		

	\\ NOTE: If local_extension is a vector, then you can ignore the value of "option" (i.e. leave it 0 or omitted).	

	
	x;y;t;

	\\ C is the list holding all polynomials in algorithm
	\\ m is the counter, c and h are temporary polynomials for algorithm  

	local(C=listcreate(),Roots=listcreate(),m=0,c,h);
	
	\\If  is a poly, then eisinit is used to return a vector defining unramified/totally ramified parts of the extension 
	if(type(local_extension)=="t_POL",
		[unram,eis,eindex]=eisinit(local_extension,p,option);	
		,unram=local_extension[1];
		eis=local_extension[2];
		eindex=poldegree(eis,y); 
	);

	findex = poldegree(unram);
	\\ building lift of roots finite field
	reps = [0];
	if(poldegree(unram,t)!=1,
		ff = ffprimroot(ffgen(Mod(1,p)*unram));
		ff = Pol(ff);
		temp_list = apply(z->Pol(ff^z),[1..(p^(poldegree(unram,t))-1)]);
		reps = concat(reps,temp_list);
		reps = apply(z->Str(z),reps);
		reps = apply(z->eval(z),reps);
	,
		reps = [0..p-1]);

	\\ For base extension finds a generator of the prime above p and finds the minpoly of the element
	\\ Use panayi to find a root of the minpoly which tells us the uniformizer in terms of the uniformizer of the local extension
	\\ if 0 then sets unifomizer to p for a trivial extension case
	nf = nfinit(base_extension);
	uniformizer = nf.zk*idealprimedec(nf,p)[1][2];
	uniformizer_minpoly = minpoly(Mod(uniformizer,base_extension));
	uniformizer_base_extension = panayi(uniformizer_minpoly ,[unram,eis] ,p)[2][1];
	if(uniformizer_base_extension ==0, uniformizer_base_extension =p,
		uniformizer_base_extension = subst(-1*polcoeff(nffactor_padic(subst(rnfequation(nfinit(unram),eis),y,x),uniformizer_minpoly,p,90)[1],0,x),t,y)
		);
	
	
	\\Finding Mod(Mod(y^(-1),eis),unram) for polsharp
	invy=Mod(Mod((eis-polcoeff(eis,0,y))/(y*polcoeff(eis,0,y)),eis),unram);

	listput(C,[gen_pol,0]);

	while(length(C)!=0&length(Roots)<40,

		for(i=1,length(C),
			c=C[1][1];
			param_apx = C[1][2];

			listpop(C,1);
	
			pol_sharp_list = polsharp_gen([c,param_apx],eis,unram,invy,eindex,p,uniformizer_base_extension,reps);
			
			
			\\breakpoint();
			if(length(pol_sharp_list)==1,
				
			
				c=pol_sharp_list[1][1]; 
				param_apx=pol_sharp_list[1][2];

				if(poldegree(Mod(subst(c,y,0),p),x)==1,m=m+1; listput(Roots,param_apx));
											
				if(poldegree(Mod(subst(c,y,0),p),x)>1,


					if(poldegree(Mod(subst(c,y,0),p),w)>0,C= concat(C,extend_generic_poly_parameter(c,uniformizer_base_extension ,reps));,
						\\ Polynomials are removed in front of the list and inserted at the end of the list
						R=polrootsff(lift(lift(Mod(subst(c,y,0),p)))*x/x,p,unram);
						for(j=1,length(R),
							h=subst(c,x,y*x+lift(lift(R[j])));
							h=lift(Mod(lift(Mod(h,eis)),unram));
							
							listput(C,[h,param_apx]);
					
						);
					);
				);
				,for(i=1,length(pol_sharp_list), listput(C,pol_sharp_list[i]));
				);
		);
		y_power = y_power+1;
	); 
	Roots = Set(apply(q->pretty_root(q,y) ,apply(z->z[2..length(z)],Roots)));
	
	
	
return([Roots,uniformizer_minpoly,unram]);
};


panayi_clean_up(Roots1,uniformizer_minpoly1,unram1,gen_poly)={
\\ base_extension = x case
if(poldegree(unram1,t)==1 & poldegree(uniformizer_minpoly1,y)==1,
	temp_roots = apply(z->lift(Mod(z,uniformizer_minpoly1)),Roots1);
	temp_roots = apply(z->lift(Mod(z,unram1)),temp_roots);
	temp_roots = apply(z->subst(gen_poly,w,z),temp_roots);
	return(temp_roots));
	
if(poldegree(unram1,t)>1 & poldegree(uniformizer_minpoly1,y)==1,
	temp_roots = apply(z->lift(Mod(z,uniformizer_minpoly1)),Roots1);
	temp_roots = apply(z->subst(z,t,y),temp_roots);
	temp_roots = apply(z->rnfequation(nfinit(subst(unram1,t,y)),subst(gen_poly,w,z)),temp_roots);
	
	
	return(temp_roots));	
	
if(poldegree(unram1,t)==1 & poldegree(uniformizer_minpoly1,y)>1,
	temp_roots = apply(z->lift(Mod(z,unram1)),Roots1);
	temp_roots = apply(z->rnfequation(nfinit(subst(uniformizer_minpoly1,t,y)),subst(gen_poly,w,z)),temp_roots);
	
	
	return(temp_roots));

if(poldegree(unram1,t)>1 & poldegree(uniformizer_minpoly1,y)>1,

	unram_in_terms_of_y = subst(nfisincl(unram1,uniformizer_minpoly1)[1],x,y);
	temp_roots = apply(z->subst(z,t,unram_in_terms_of_y),Roots1);
	temp_roots = apply(z->rnfequation(nfinit(subst(uniformizer_minpoly1,t,y)),subst(gen_poly,w,z)),temp_roots);
	
	
	return(temp_roots));

}


nffactor_padic(unram,A,p,precision)={
	local(k=0,j=0,unram_temp);
	unram_temp = subst(unram,x,t);
	while(j==0,
		N=polresultant(subst(unram_temp,t,y),subst(A,x,x-k*y),y);
		M=factorpadic(N,p,precision);
		a=0;	
		i=1;
		while(a==0 & i<=length(M[,2]),
			if(M[i,2]>1,a=1);
			i=i+1;

		);
		if(a==0,j=1,k=k+1);
	);

poly_list = M[,1];

poly_list = apply(z->gcd(A,Mod(subst(z,x,x+k*t),unram_temp)),poly_list);
poly_list = apply(z->z/polcoeff(z,poldegree(z),x),poly_list);
poly_list = apply(z->lift(lift(z)),poly_list);

\\ R=gcd(A,Mod(subst(M[1,1],x,x+k*t),unram_temp));	
\\ R=R/polcoeff(R,poldegree(R),x);
\\ eis=lift(subst(lift(R),x,y));
\\ return(eis)

return(poly_list);
}


pretty_root(list,uniformizer_base_extension)={
	output = 0;
	for(i=1,length(list),output=output+list[i]*uniformizer_base_extension^(i-1));
	return(output)
}


\\ Extends the parameter of a generic polynomial out one spot
extend_generic_poly_parameter(f,uniformizer_base_extension ,reps)={
	return(apply(z->[subst(f[1],w,z+uniformizer_base_extension*w),concat(f[2],z)],reps));
};

\\ Valuation of a poly in terms of w (with respect to y)
ufval_fi(fi,eis,eindex,p)={
	\\ valuation of coeffs of w
	val_w_coeffs = apply(z->ufval_element(polcoef(fi,z,w),eis,eindex,p),[1..poldegree(fi,w)]);
	val_w_coeffs = concat(val_w_coeffs,+oo);

	\\ valuation of constant coeff
	val_const_coeffs = apply(z->ufval_element(polcoef(fi,z,w),eis,eindex,p),[0]);
	val_const_coeffs = concat(val_const_coeffs, +oo);

	if(vecmin(val_const_coeffs )<vecmin(val_w_coeffs ),return(vecmin(val_const_coeffs )),return(+oo));

}

\\ valution of gen poly
ufval_gen_poly(f,eis,eindex,p)={
	val_coeffs = apply(z->ufval_fi(polcoef(f,z,x),eis,eindex,p),[0..poldegree(f,x)]);
	if(vecsum(apply(z->z==+oo,val_coeffs))>0, return(+oo),return(vecmin(val_coeffs)));
}


polsharp_gen(f,eis,unram,invy,eindex,p,uniformizer_base_extension,reps)={
	local(n,v,h);
	h=lift(Mod(lift(Mod(f[1],eis)),unram));
	v=ufval_gen_poly(h,eis,eindex,p);
	if(v==+oo,return(extend_generic_poly_parameter([h,f[2]],uniformizer_base_extension ,reps)),return([[lift(Mod(lift(Mod(h*invy^(v),eis)),unram)),f[2]]] ));
};


\\ Finds the valuation of an element 
ufval_element(element,eis,eindex,p)={
	local(n,v);
	n=poldegree(element,y);
	v=+oo;
	for(j=0,n,
		if(polcoeff(element,j,y)!=0,
			v=min(v,eindex*valuation(polcoeff(element,j,y),p)+j);
		);
	);
	return(v);
};


panayi_improved(f,g,p,option) =
{
	\\ Finds the number of roots f (in terms of x) has in K, an extension of Q_p defined by the input g.
	\\ The input g can either be a polynomial (in terms of x), so K will be Q_p adjoined a root of g,
	\\ or a 2-component vector that defines that unramified/totally ramified parts of K,
	\\ where the first entry is a polynomial that defines an unramified extension (in terms of t) and 
	\\ the second entry is an eisenstien polynomial over the unramified extension (in terms of y) 

	\\ There are two implementations of Panayi's Algorithm. 
	
	\\ Implementation 1: Uses the command polrootsff to find the needed roots modulo the prime ideal above p, 
	\\ but method needs polynomials defining unramified/totally ramified parts of the extension. So if g is a polynomial and 
	\\ not a vector, then the implementation will find polynomials defined unramified/totally ramified parts of the extension and 
	\\ uses the "option" value to determine on how to find them. 
	\\ When g is a polynomial and when option is 0 or omitted, then uses a lexiographical ordering to find the polynomial defining unramified part of the extension K  	
	\\ When g is a polynomial and when option is 1, then the command ffinit to define unramified part of the extension K  		

	\\ NOTE: If g is a vector, then you can ignore the value of "option" (i.e. leave it 0 or omitted).	
	
	\\ Implementation 2: Uses the command nffactormod to find the needed roots, g needs to be polynomial with integer coefficients. 
	\\ To use implementation 2, set "option" equal to 2.
	
	x;y;t;

	\\ Uses second implementation of Panayi's Algorithm 
	if(option==2,return(panayi1(f,g,p)));

	\\ C is the list holding all polynomials in algorithm
	\\ m is the counter, c and h are temporary polynomials for algorithm  

	local(C=listcreate(),Roots=listcreate(),m=0,c,h);
	
	
	\\If g is a poly, then eisinit is used to return a vector defining unramified/totally ramified parts of the extension 
	if(type(g)=="t_POL",
		[unram,eis,eindex]=eisinit(g,p,option);	
		,unram=g[1];
		eis=g[2];
		eindex=poldegree(eis,y); 
	);

	\\Finding Mod(Mod(y^(-1),eis),unram) for polsharp
	invy=Mod(Mod((eis-polcoeff(eis,0,y))/(y*polcoeff(eis,0,y)),eis),unram);

	f=polsharp(f,eis,unram,invy,eindex,p);
	listput(C,[f,[0]]);
	y_power = 0;
	while(length(C)!=0,
		for(i=1,length(C),
			c=C[1][1];
			root_apx = C[1][2];
			listpop(C,1); \\ Polynomials are removed in front of the list and inserted at the end of the list
			R=polrootsff(subst(c,y,0),p,unram);
			for(j=1,length(R),
				h=subst(c,x,y*x+lift(lift(R[j])));
				h=lift(Mod(lift(Mod(h,eis)),unram));
				h=polsharp(h,eis,unram,invy,eindex,p);
				if(poldegree(Mod(subst(h,y,0),p),x)==1 & length(root_apx)>eindex-1,m=m+1; root_apx = concat(root_apx,lift(lift(R[j])));  listput(Roots,root_apx),listput(C,[h,concat(root_apx,lift(lift(R[j]))) ]);root_apx = concat(root_apx,lift(lift(R[j]))););
				if(poldegree(Mod(subst(h,y,0),p),x)>1,listput(C,[h,concat(root_apx,lift(lift(R[j]))) ]));
				
			);
		);
	);
	\\ Roots = Set(apply(q->pretty_root(q,y) ,apply(z->z[2..length(z)],Roots)));
return([m,Roots]);
};



panayi(f,g,p,option) =
{
	\\ Finds the number of roots f (in terms of x) has in K, an extension of Q_p defined by the input g.
	\\ The input g can either be a polynomial (in terms of x), so K will be Q_p adjoined a root of g,
	\\ or a 2-component vector that defines that unramified/totally ramified parts of K,
	\\ where the first entry is a polynomial that defines an unramified extension (in terms of t) and 
	\\ the second entry is an eisenstien polynomial over the unramified extension (in terms of y) 

	\\ There are two implementations of Panayi's Algorithm. 
	
	\\ Implementation 1: Uses the command polrootsff to find the needed roots modulo the prime ideal above p, 
	\\ but method needs polynomials defining unramified/totally ramified parts of the extension. So if g is a polynomial and 
	\\ not a vector, then the implementation will find polynomials defined unramified/totally ramified parts of the extension and 
	\\ uses the "option" value to determine on how to find them. 
	\\ When g is a polynomial and when option is 0 or omitted, then uses a lexiographical ordering to find the polynomial defining unramified part of the extension K  	
	\\ When g is a polynomial and when option is 1, then the command ffinit to define unramified part of the extension K  		

	\\ NOTE: If g is a vector, then you can ignore the value of "option" (i.e. leave it 0 or omitted).	
	
	\\ Implementation 2: Uses the command nffactormod to find the needed roots, g needs to be polynomial with integer coefficients. 
	\\ To use implementation 2, set "option" equal to 2.
	
	x;y;t;

	\\ Uses second implementation of Panayi's Algorithm 
	if(option==2,return(panayi1(f,g,p)));

	\\ C is the list holding all polynomials in algorithm
	\\ m is the counter, c and h are temporary polynomials for algorithm  

	local(C=listcreate(),Roots=listcreate(),m=0,c,h);
	
	
	\\If g is a poly, then eisinit is used to return a vector defining unramified/totally ramified parts of the extension 
	if(type(g)=="t_POL",
		[unram,eis,eindex]=eisinit(g,p,option);	
		,unram=g[1];
		eis=g[2];
		eindex=poldegree(eis,y); 
	);

	\\Finding Mod(Mod(y^(-1),eis),unram) for polsharp
	invy=Mod(Mod((eis-polcoeff(eis,0,y))/(y*polcoeff(eis,0,y)),eis),unram);

	f=polsharp(f,eis,unram,invy,eindex,p);
	listput(C,[f,[0]]);
	y_power = 0;
	while(length(C)!=0,
		for(i=1,length(C),
			c=C[1][1];
			root_apx = C[1][2];
			listpop(C,1); \\ Polynomials are removed in front of the list and inserted at the end of the list
			R=polrootsff(subst(c,y,0),p,unram);
			for(j=1,length(R),
				h=subst(c,x,y*x+lift(lift(R[j])));
				h=lift(Mod(lift(Mod(h,eis)),unram));
				h=polsharp(h,eis,unram,invy,eindex,p);
				if(poldegree(Mod(subst(h,y,0),p),x)==1,m=m+1; root_apx = concat(root_apx,lift(lift(R[j])));  listput(Roots,root_apx));
				if(poldegree(Mod(subst(h,y,0),p),x)>1,listput(C,[h,concat(root_apx,lift(lift(R[j]))) ]));
				
			);
		);
	);
	Roots = Set(apply(q->pretty_root(q,y) ,apply(z->z[2..length(z)],Roots)));
return([m,Roots]);
};


\\ Finds the valuation of the i th coefficient of f 
ufval(f,eis,eindex,p,i)={
	local(n,fi,v);
	fi=polcoeff(f,i,x);
	n=poldegree(fi,y);
	v=+oo;
	for(j=0,n,
		if(polcoeff(fi,j,y)!=0,
			v=min(v,eindex*valuation(polcoeff(fi,j,y),p)+j);
		);
	);
	return(v);
};


\\ Evaluates each coefficient using ufval, finds the minimal valuation (v), multiplies f by invy^(v) 
\\ and reduces coefficients by modding by eis and unram and then lifting.
polsharp(f,eis,unram,invy,eindex,p)={
	local(n,v,h);
	h=lift(Mod(lift(Mod(f,eis)),unram));
	n=poldegree(f);
	v=ufval(h,eis,eindex,p,0);
	for(i=1,n,
		v=min(v, ufval(h,eis,eindex,p,i));
	);
	return(lift(Mod(lift(Mod(h*invy^(v),eis)),unram)));
};

\\ When g is a polynomial, eisinit finds polynomials defining the unramified/totally ramified parts
\\ of the extension. When "option" is 0 or omitted, then a lexiographical ordering is used to find the polynomial defining
\\ unramified extension. If "option" is 1, use ffinit to find the polynomial.
\\ NOTE: eisinit uses factorpadic at 500 precision, to find the polynomial defined the totally ramified part of the extension. 
eisinit(g,p,option)={
	
	local(k=0,j=0,findex,eindex);

	nf=nfinit([g,[p]]);
	id=idealprimedec(nf,p)[1];
	findex=id[4];
	eindex=id[3];
	A=minpoly(Mod(nf.zk*id[2],g));
	if(option==0,  unram=unrampoljr(findex,p),unram=lift(ffinit(p,findex,t)));
	
	if(eindex==1,return([unram,y-p,eindex]));
	if(findex==1,return([unram,subst(A,x,y),eindex]));
			
	while(j==0,

		N=polresultant(subst(unram,t,y),subst(A,x,x-k*y),y);
		M=factorpadic(N,p,500);
		a=0;	
		i=1;
		while(a==0 & i<=length(M[,2]),
			if(M[i,2]>1,a=1);
			i=i+1;

		);
		if(a==0,j=1,k=k+1);
	);

R=gcd(A,Mod(subst(M[1,1],x,x+k*t),unram));	
R=R/polcoeff(R,eindex,x);
eis=subst(lift(R),x,y);
return([unram,eis,eindex]);		
};



\\ Next 3 commands are used to find the polynomial defininig the unramified part
\\ of the extension using a lexiographical ordering
isirredmodp(pol, p) = poldegree(pol) == poldegree(factormod(pol,p)[1,1]);

isprimpol(pol,p) ={

  	local(m,od, pps);

	m=poldegree(pol);
	pol=pol*Mod(1,p);
	od=p^m-1;            /* Order of the group */
	pps=factor(od)[,1]~; /* primes dividing the order of the group */
	for(j=1,length(pps),
		if(lift(lift(Mod(x,pol)^(od/pps[j]))) == 1, return(0)));

	return(1);
};

unrampoljr(m, p)={

	local(trying, pol, j,s);

	trying=1;
	pol=t^m;
	while(trying,
		j=0; s=1;
    		while(polcoeff(pol,j)==(p-1)*s, pol -= s*(p-1)*t^j;s= -s;j++);
   	pol += s*t^j;
   	if(isirredmodp(pol, p), if(isprimpol(pol,p), trying=0)));

	pol

};



\\ The second method of Panayi's algorithm
panayi1(f,g,p) =
{

	\\ C is the list holding all polynomials in algorithm
	\\ m is the counter, c and h are temporary polynomials for algorithm  
	\\ uf is the uniformizer
	\\ u will represent the adjoined root of g
	local(C=listcreate(),m=0,c,h);
	
	g=subst(g,x,u);
	nf=nfinit([g,p]);
	
	\\Various structures representing the ideal above p, used for future commands
	id=idealprimedec(nf,p);

	if(#id==1,

	id=id[1];
	pr=nfmodprinit(nf,id);

	\\Finds uniformizer, uf, in terms of u
	
	if(id[3]==1, uf=p, uf=nf.zk*id[2]);

	uf=Mod(uf,g);
	invuf=uf^(-1);
	f=Mod(f,g);
	f=polsharp1(f,g,id,nf,invuf);
	listput(C,f);
	while(length(C)!=0,
		for(i=1,length(C),
			c=C[1];
			listpop(C,1); \\ Polynomials are removed in front of the list and inserted at the end of the list

			\\ Using polrootsmodpr command to find the lifted roots of c mod the prime ideal above p
			R=polrootsmodpr(c,nf,id,g);
			for(j=1,length(R),
				h=subst(c,x,uf*x+R[j]);
				h=polsharp1(h,g,id,nf,invuf);
				if(poldegree(polreducemodpr(h,nf,pr),x)==1,m=m+1);
				if(poldegree(polreducemodpr(h,nf,pr),x)>1,listput(C,h));
				
			);
		);
	);
, print("Polynomial is not irreducible");
	);
return(m);
};



\\ Finds the minimal valuation of all the coeffs of f and divides by appropriate power of uf 
\\rewrites coefficients in terms of 1,u,...,u^(n-1) by modding by g and then lifting.
polsharp1(f,g,id,nf,invuf)={	
	local(n,v);

	n=poldegree(f,x);
	v=nfeltval(nf,polcoeff(f,0,x),id);
	for(i=1,n,
		v=min(v, nfeltval(nf,polcoeff(f,i,x),id));
	);

	return(f*invuf^v);
};


\\Computes f mod the prime ideal above p
polreducemodpr(f,nf,pr)={
	local(n,poly=0);
	
	n=poldegree(f,x);
	for(i=0,n,
		poly=poly+nfmodpr(nf,polcoeff(f,i,x),pr)*x^i;
	
	);
	return(poly);
	
};


\\Finds roots mod the prime ideal above p, by factoring and finding linear factors
\\root are checked if it belongs in the ring of integers
polrootsmodpr(c,nf,id,g)={
	local(F,roots=[]);

	F=nffactormod(nf,c,id);
	F=Mod(F,g);
	for(i=1,length(F[,2]),
		if(poldegree(F[i,1],x)==1 ,
			roots=concat(roots,-1*polcoeff(F[i,1],0,x)/polcoeff(F[i,1],1,x));
		);
	);

return(roots);
};
