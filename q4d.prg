havoc m,n;
assume m >= 0;
assume n >= 0;
res := 0;
m1 := m;
while (m1 < 0 or m1 > 0)
inv 0<= m1 and m1 <= m and res = (m-m1)*n
do
{
n1 := n;
old_res := res;

while (n1>0 or n1 <0)
inv 0<=n1 and n1<=n and res = old_res + (n-n1)
do
{
 res := res+1;
 n1 := n1-1
};
m1 := m1-1
};
assert res = m * n
