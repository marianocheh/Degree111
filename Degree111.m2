


	
	
	
	


loadPackage "Schubert2" 
n=3; 
P1 = abstractProjectiveSpace'(1, VariableName => h1);
R1 = intersectionRing P1;
c1= chern tangentBundle P1; 
s1 = segre dual(tangentBundle P1); 
P1n= abstractProjectiveSpace'(n, VariableName => h2); 
R1n = intersectionRing P1n; 
c1n = chern tangentBundle P1n; 
s1n= segre dual(tangentBundle P1n); 
P2n= abstractProjectiveSpace'(n, VariableName => h3); 
R2n = intersectionRing P2n; 
c2n = chern tangentBundle P2n; 
s2n= segre dual(tangentBundle P2n); 
P3n= abstractProjectiveSpace'(n, VariableName => h4); 
R3n = intersectionRing P3n; 
c3n = chern tangentBundle P3n; 
s3n= segre dual(tangentBundle P3n); 
Pe1= abstractProjectiveSpace'(3*n+1, VariableName => e1); 
Re1 = intersectionRing Pe1; 
Phe1= abstractProjectiveSpace'(3*n, VariableName => he1); 
Rhe1 = intersectionRing Phe1; 
Pe2= abstractProjectiveSpace'(3*n+1, VariableName => e2); 
Re2 = intersectionRing Pe2; 
RX=(R1 ** R1n ** R2n ** R3n ** Re1 ** Re2 ** Rhe1); 
sNB0rX= sub(s1n^2,RX); 
B0r=sub(0,RX); 
for i from 0 to n do (for j from 0 to n do (B0r=B0r+h2^i*h3^j*h4^(2*n-i-j))); 
cNB0rX= sub(c1n^2,RX); 
cTX=sub(c1,RX)*sub(c1n,RX)*sub(c2n,RX)*sub(c3n,RX); 
sTX=sub(s1,RX)*sub(s1n,RX)*sub(s2n,RX)*sub(s3n,RX); 
cTPnO1=sub(1,RX); 
for k from 1 to n do (cTPnO1=cTPnO1+part(k,(1+h2)^(n+1))+(n-k+1)*h1*part(k-1,(1+h2)^(n+1))); 
sTPnO1=sub(1,RX); 
for k from 1 to n+1 do (sTPnO1=sTPnO1+part(k,sub(s1n,RX))-(n+k-1)*h1*part(k-1,sub(s1n,RX))); 
cNB0XB0r=cTPnO1; 
sNB0XB0r=sTPnO1; 
cNB0'rE'=sub(1,RX); 
for k from 1 to n do (z=part(k,cNB0XB0r); for i from 1 to k do (z = z + binomial(n-k+i,i) * (he1)^i * part(k-i,cNB0XB0r)); cNB0'rE'=cNB0'rE'+z); 
sNB0'rE'=sub(1,RX); 
for k from 1 to 2*n do (z=part(k,sNB0XB0r); for i from 0 to k-1 do (z = z + (-1)^(k-i) * binomial(n-1+k,n-1+i) * (he1)^(k-i) * part(i,sNB0XB0r)); sNB0'rE'=sNB0'rE'+z); B0'r=sub(part(n,cNB0'rE'),{he1=>-e1})*e1; 
cNB0'rX'=cNB0'rE' * (1-he1); 
sNE'X'=sub(1,RX); 
for k from 1 to 3*n do (sNE'X'=sNE'X'+(he1)^k); 
sNB0'rX'=sNB0'rE' *sNE'X'; 
cNB0'rX'=sub(cNB0'rX',{he1=>-e1}); 
sNB0'rX'=sub(sNB0'rX',{he1=>-e1}); 
B1=sub(0,RX); 
for i from 0 to n do (B1=B1+h1*h3^i*h4^(n-i)); 
B2=sub(0,RX); 
for i from 0 to n do (B2=B2+h1*h2^i*h4^(n-i)); 
B3=sub(0,RX); 
for i from 0 to n do (B3=B3+h1*h2^i*h3^(n-i)); 
cTZ1=sub(c1,RX)*sub(c1n,RX)*sub(c2n,RX); 
cTZ2=sub(c1,RX)*sub(c1n,RX)*sub(c2n,RX); 
cTZ3=sub(c1,RX)*sub(c1n,RX)*sub(c3n,RX); 
sNZ1X=sTX*cTZ1; 
sNZ2X=sTX*cTZ2; 
sNZ3X=sTX*cTZ3; 
sNZ1tX'=sub(1,RX); 
for k from 1 to 2*n+1 do (z=part(k,sNZ1X); for i from 0 to k-1 do (z = z +  binomial(n-1+k,n-1+i) * (e1)^(k-i) * part(i,sNZ1X)); sNZ1tX'=sNZ1tX'+z);
sNZ2tX'=sub(1,RX); 
for k from 1 to 2*n+1 do (z=part(k,sNZ2X); for i from 0 to k-1 do (z = z + binomial(n-1+k,n-1+i) * (e1)^(k-i) * part(i,sNZ2X)); sNZ2tX'=sNZ2tX'+z); 
sNZ3tX'=sub(1,RX); 
for k from 1 to 2*n+1 do (z=part(k,sNZ3X); for i from 0 to k-1 do (z = z +  binomial(n-1+k,n-1+i) * (e1)^(k-i) * part(i,sNZ3X)); sNZ3tX'=sNZ3tX'+z); 
sNB1''X''=sub(1,RX); 
for k from 1 to 2*n do (z=part(k,sNZ1tX'); for i from 0 to k-1 do (z = z +  binomial(n-1+k,n-1+i) * (e2)^(k-i) * part(i,sNZ1tX')); sNB1''X''=sNB1''X''+z); 
sNB2''X''=sub(1,RX); 
for k from 1 to 2*n do (z=part(k,sNZ2tX'); for i from 0 to k-1 do (z = z +  binomial(n-1+k,n-1+i) * (e2)^(k-i) * part(i,sNZ2tX')); sNB2''X''=sNB2''X''+z); 
sNB3''X''=sub(1,RX); 
for k from 1 to 2*n do (z=part(k,sNZ3tX'); for i from 0 to k-1 do (z = z +  binomial(n-1+k,n-1+i) * (e2)^(k-i) * part(i,sNZ3tX')); sNB3''X''=sNB3''X''+z); 
sNB1B0rB1= sub(s1n,RX); 
sNB2B0rB2= sub(s2n,RX); 
sNB3B0rB3= sub(s3n,RX); 
sNE'X'=sub(1,RX); 
for k from 1 to (3*n) do sNE'X'=sNE'X'+(-e1)^k ; 
F11 =part(n+1, cNB0rX* sNE'X' * e1 * h1 * sNB1B0rB1); 
F12 =part(n+1, cNB0rX*sNE'X' * e1 * h1 * sNB2B0rB2); 
F13 =part(n+1, cNB0rX*sNE'X' * e1 * h1 * sNB3B0rB3); 
B1t = B1-F11; 
B2t = B2-F12; 
B3t = B3-F13; 
sNB1'B0'rB1'=sub(1,RX); 
for k from 1 to (3*n) do sNB1'B0'rB1'=sNB1'B0'rB1'+(-e1)^k ; 
sNB2'B0'rB2'=sNB1'B0'rB1'; 
sNB3'B0'rB3'=sNB1'B0'rB1'; 
sNE''X''=sub(1,RX); 
for k from 1 to (3*n) do sNE''X''=sNE''X''+(-e2)^k ; 
F21= part(n+1,cNB0'rX' * e2 * sNE''X'' * h1 * sNB1'B0'rB1'); 
F22= part(n+1,cNB0'rX' * e2 * sNE''X'' * h1 * sNB2'B0'rB2'); 
F23= part(n+1,cNB0'rX' * e2 * sNE''X'' * h1 * sNB3'B0'rB3'); 
B1tt = B1t-F21; 
B2tt = B2t-F22; 
B3tt = B3t-F23; 
ResTot=1/6*(h1+h2+h3+h4-e1-e2)^(3*n+1); 
for j from (n+1) to (3*n+1) do (ResTot = ResTot - 1/6 * binomial(3*n+1,j) * part(j-n-1,sNB1''X'') * B1tt * (h1+h2+h3+h4-e1-e2)^(3*n+1-j)- 1/6 * binomial(3*n+1,j) * part(j-n-1,sNB2''X'') * B2tt * (h1+h2+h3+h4-e1-e2)^(3*n+1-j)- 1/6 *binomial(3*n+1,j) * part(j-n-1,sNB3''X'') * B3tt * (h1+h2+h3+h4-e1-e2)^(3*n+1-j));
ResAux=sub(part(0,sub(ResTot,QQ[h1,h2,h3,h4,e1,e2,Degrees=>{0,0,0,0,0,1}])),RX);
P=(3*n+2):sub(0,RX); 
for j from 0 to 3*n+1 do (P=replace(j,sub(sub(part(j,sub(ResTot,QQ[h1,h2,h3,h4,e1,e2,Degrees=>{0,0,0,0,0,1}])),RX),{sub(e2,RX)=>sub(1,RX)}),P)); 
for j from (n+1) to (3*n+1) do (ResAux = ResAux+P_j*(-1)^(j-1)*part(j-n-1,sNB0'rX')*B0'r);
ResFin=sub(part(0,sub(ResAux,QQ[h1,h2,h3,h4,e1,Degrees=>{0,0,0,0,1}])),RX); 
Q=(3*n+2):sub(0,RX); 
for j from 0 to 3*n+1 do (Q=replace(j,sub(sub(part(j,sub(ResAux,QQ[h1,h2,h3,h4,e1,Degrees=>{0,0,0,0,1}])),RX),{sub(e1,RX)=>sub(1,RX)}),Q)); 
for j from (2*n) to (3*n+1) do (ResFin= ResFin+Q_j*(-1)^(j-1)*part(j-2*n,sNB0rX)*B0r); 
ResFin 
sub(ResFin,{sub(h1,RX)=>sub(1,RX),sub(h2,RX)=>sub(1,RX),sub(h3,RX)=>sub(1,RX),sub(h4,RX)=>sub(1,RX)}) 
