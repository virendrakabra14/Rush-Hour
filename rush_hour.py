from z3 import *
import sys

verticals = []
horizontals = []
mines = []
R = []
n = 0
moves = 0


def input_():

    # input
    input_file = open(sys.argv[1],'r')
    input_lines = input_file.readlines()

    global verticals ,horizontals,mines,R,n ,moves
    # n,moves = [int(x) for x in input().split(',')]
    n,moves = [int(x) for x in input_lines[0].split(',')]

    R = [ [ 0 for j in range(n) ]
            for i in range(n) ]
    sat_r = [[Bool]]
    # ri,rj = [int(x) for x in input().split(',')]
    ri,rj = [int(x) for x in input_lines[1].split(',')]
    R[ri][rj] = 1
    R[ri][rj+1] = 1
    inp_list = []
    # while(1):
    #     t = input().split(',')
    #     if t==['']:
    #         break
    #     x,y,z= [int(x) for x in t]
        
    #     inp_list.append([x,y,z])
    for index in range(2,len(input_lines)):
        t = input_lines[index].split(',')
        x,y,z = [int(x1) for x1 in t]
        inp_list.append([x,y,z])

    for p in range(len(inp_list)):
        i,j,k = inp_list[p]
        if i == 0:
            v = [ [ 0 for j in range(n) ]
                for i in range(n) ]
            
            v[j][k] = 1
            v[j+1][k] = 1
            verticals.append(v)

        elif i == 1:
            h = [ [ 0 for j in range(n) ]
                for i in range(n) ]
                
            
            h[j][k] = 1
            h[j][k+1] = 1
            horizontals.append(h)

        else:
            m =  [ [ 0 for j in range(n) ]
                for i in range(n) ]
            m[j][k] = 1
            mines.append(m)

input_()

#utility func, default abs does not work with z3 int
def abs(x):
    return If(x >= 0,x,-x)

#combine R,mines,hor and vert arrays into one matrix (for visualisation and debugging)
def combine(model):
    comb = [[0 for i in range(n)] for j in range(n)]
    for i in range(n):
        for j in range(n):
            for x in model[1]:
                if x[i][j]==1:
                    comb[i][j]=1
            for x in model[2]:
                if x[i][j]==1:
                    comb[i][j]=1
            for x in model[3]:
                if x[i][j]==1:
                    comb[i][j]=1
            if model[0][i][j]==1:
                comb[i][j]=1
    return comb

#format z3's output into nice format ([R,mines,horizontals,verticals])
# since z3 returns a dictionary
def model_formatter(model,sat_r,sat_m,sat_h,sat_v):
    R_for = [[0 for i in range(n)] for j in range(n)]
    for i in range(n):
        for j in range(n):
            if model[sat_r[i][j]]==1:
                R_for[i][j]=1

    verticals_for = [[[0 for i in range(n)]for j in range(n)]for k in range(len(sat_v))]
    for i in range(len(sat_v)):
        for j in range(n):
            for k in range(n):
                if model[sat_v[i][j][k]]==1:
                    verticals_for[i][j][k]=1

    horizontals_for = [[[0 for i in range(n)]for j in range(n)]for k in range(len(sat_h))]
    for i in range(len(sat_h)):
        for j in range(n):
            for k in range(n):
                if model[sat_h[i][j][k]]==1:
                    horizontals_for[i][j][k]=1

    mines_for = [[[0 for i in range(n)]for j in range(n)]for k in range(len(sat_m))]
    for i in range(len(sat_m)):
        for j in range(n):
            for k in range(n):
                if model[sat_m[i][j][k]]==1:
                    mines_for[i][j][k]=1
    return [R_for,mines_for,horizontals_for,verticals_for]


def solve_step(R,mines,horizontals,verticals,cond_list):
    s = Solver()
    # Horizontal condition
    l = 0
    sat_h = []
    for x in horizontals:
        sat_h.append([[Int('H'+str(l)+'_'+str(p)+'_'+str(q)) for p in range(n)]for q in range(n)])
        for i in range(n):
            count = 0
            for j in range(n):
                s.add(sat_h[l][i][j]>=0)# couldhave used bool but arithmetic operations on Bool and type casting are
                s.add(sat_h[l][i][j]<=1)# not allowed

                if(x[i][j]==True and (j==0 or x[i][j-1]!=True)):
                    count = 1
                    #since all possible states are predefined below, only one block movement is possible.
                    if(j!=0 and j<n-2): # for the case ...|  0  |  1 | 1  | 0  |..., 
                                        #we can have |  1  |  1 | 0  | 0  | or | 0 | 0 |  1  |  1  |
                                        #along with the original configuration
                        s.add(Or(Or(And(sat_h[l][i][j]+sat_h[l][i][j+1]==2,sat_h[l][i][j+2]+sat_h[l][i][j-1]==0),
                        And(sat_h[l][i][j-1]+sat_h[l][i][j]==2,sat_h[l][i][j+1]+sat_h[l][i][j+2]==0)),
                        And(sat_h[l][i][j+1]+sat_h[l][i][j+2]==2,sat_h[l][i][j]+sat_h[l][i][j-1]==0)))
                    #for case when on one side the movement is restricted
                    elif(j==0):
                        s.add(Or(And(sat_h[l][i][j+1]+sat_h[l][i][j+2]==2,sat_h[l][i][j]==0),And(sat_h[l][i][j+1]+sat_h[l][i][j]==2,sat_h[l][i][j+2]==0)))
                    elif(j==(n-2)):
                        s.add(Or(And(sat_h[l][i][j+1]+sat_h[l][i][j]==2,sat_h[l][i][j-1]==0),And(sat_h[l][i][j-1]+sat_h[l][i][j]==2,sat_h[l][i][j+1]==0)))
            if count == 1: #makes sure that only 2 1's are possible in one row
                sum = sat_h[l][i][0]
                for h in range(1,n):
                    sum += sat_h[l][i][h]
                s.add(sum==2) 

            if count == 0:#makes sure all values are 0 in row if there were no 1s in the original input row
                sum = sat_h[l][i][0]
                for h in range(1,n):
                    sum += sat_h[l][i][h]
                s.add(sum==0) 
        l+=1

    l =0 # same as horizontal with indices flipped.
    sat_v = []
    for x in verticals:
        sat_v.append([[Int('V'+str(l)+'_'+str(p)+'_'+str(q)) for p in range(n)]for q in range(n)])
        for j in range(n):
            count = 0
            for i in range(n):
                s.add(sat_v[l][i][j]>=0)
                s.add(sat_v[l][i][j]<=1)

                if(x[i][j]==1 and (i==0 or x[i-1][j]!=1)):
                    count = 1
                    if(i!=0 and i<n-2):
                        s.add(Or(Or(And(sat_v[l][i][j]+sat_v[l][i+1][j]==2,sat_v[l][i+2][j]+sat_v[l][i-1][j]==0),
                        And(sat_v[l][i-1][j]+sat_v[l][i][j]==2,sat_v[l][i+1][j]+sat_v[l][i+2][j]==0)),
                        And(sat_v[l][i+1][j]+sat_v[l][i+2][j]==2,sat_v[l][i][j]+sat_v[l][i-1][j]==0)))
                    elif(i==0):
                        s.add(Or(And(sat_v[l][i+1][j]+sat_v[l][i+2][j]==2,sat_v[l][i][j]==0),And(sat_v[l][i+1][j]+sat_v[l][i][j]==2,sat_v[l][i+2][j]==0)))
                    elif(i==(n-2)):
                        s.add(Or(And(sat_v[l][i+1][j]+sat_v[l][i][j]==2,sat_v[l][i-1][j]==0),And(sat_v[l][i-1][j]+sat_v[l][i][j]==2,sat_v[l][i+1][j]==0)))
            
            if count == 1:
                sum = sat_v[l][0][j]
                for h in range(1,n):
                    sum += sat_v[l][h][j]
                s.add(sum==2) 

            if count == 0:
                sum = sat_v[l][0][j]
                for h in range(1,n):
                    sum += sat_v[l][h][j]
                s.add(sum==0) 
        l+=1

    l = 0
    sat_m = []# no movement conditions as mines are fixed
    for x in mines:
        sat_m.append([[Int('M'+str(l)+'_'+str(p)+'_'+str(q)) for p in range(n)]for q in range(n)])
        for j in range(n):
            for i in range(n):
                if(x[i][j]==1):
                    s.add(sat_m[l][i][j] == 1) #fix the position of mine
                else:
                    s.add(sat_m[l][i][j]==0)
        l+=1
    
    l = 0
    #same as for horizontal 
    sat_r=[[Int('R'+str(l)+'_'+str(p)+'_'+str(q)) for p in range(n)]for q in range(n)]
    for i in range(n):
        count = 0
        for j in range(n):
            s.add(sat_r[i][j]>=0)
            s.add(sat_r[i][j]<=1)

            if(R[i][j]==1 and (j==0 or R[i][j-1]!=1)):
                count = 1
                if(j!=0 and j<n-2):
                    s.add(Or(Or(And(sat_r[i][j]+sat_r[i][j+1]==2,sat_r[i][j+2]+sat_r[i][j-1]==0),
                    And(sat_r[i][j-1]+sat_r[i][j]==2,sat_r[i][j+1]+sat_r[i][j+2]==0)),
                    And(sat_r[i][j+1]+sat_r[i][j+2]==2,sat_r[i][j]+sat_r[i][j-1]==0)))
                elif(j==0):
                    s.add(Or(And(sat_r[i][j+1]+sat_r[i][j+2]==2,sat_r[i][j]==0),And(sat_r[i][j+1]+sat_r[i][j]==2,sat_r[i][j+2]==0)))
                elif(j==(n-2)):
                    s.add(Or(And(sat_r[i][j+1]+sat_r[i][j]==2,sat_r[i][j-1]==0),And(sat_r[i][j-1]+sat_r[i][j]==2,sat_r[i][j+1]==0)))
        if count == 1:
            sum = sat_r[i][0]
            for h in range(1,n):
                sum += sat_r[i][h]
            s.add(sum==2) 

        if count == 0:
            sum = sat_r[i][0]
            for h in range(1,n):
                sum += sat_r[i][h]
            s.add(sum==0) 

    #merge all separate board components into a common 2D-array
    

    sum_total = [[Int('Sum_tot_'+str(p)+'_'+str(q)) for p in range(n)]for q in range(n)]
    for i in range(n):
        for j in range(n):
            sum_total[i][j] = sat_r[i][j]
            for x in range(len(sat_m)):
                sum_total[i][j] += sat_m[x][i][j]
            for x in range(len(sat_h)):
                sum_total[i][j] += sat_h[x][i][j]
            for x in range(len(sat_v)):
                sum_total[i][j] += sat_v[x][i][j]
            s.add(sum_total[i][j]<=1)
    #constrain the sum of absolute difference between the current board and predicted model to be equal to 2
    #all board pieces could move only 1 block but they all can move together which is not wanted.
    # this constraint allows only 2 blocks of the predicted model to be different from the input state.
    #ensuring exactly one move for the entire board.
    abs_sum = abs(sat_r[0][0]-R[0][0])
    for i in range(n):
        for j in range(n):
            if i!=0 or j!=0:
                abs_sum+=abs(sat_r[i][j]-R[i][j])
            for x in range(len(verticals)):
                abs_sum += abs(sat_v[x][i][j]-verticals[x][i][j])
            for x in range(len(mines)):
                abs_sum += abs(sat_m[x][i][j]-mines[x][i][j])
            for x in range(len(horizontals)):
                abs_sum += abs(sat_h[x][i][j]-horizontals[x][i][j])
    # for i in range(n):
    #     for j in range(n):
    #         if i==0 and j==0:
    #             continue
    #         abs_sum+=abs(sum_total[i][j]-curr_board[i][j])
    s.add(abs_sum==2)

    #storing names of all sat variables for easy access
    var_list = []
    for i in range(n):
        for j in range(n):
            var_list.append(sat_r[i][j])
            for x in sat_h:
                var_list.append(x[i][j])
            for x in sat_v:
                var_list.append(x[i][j])


    t = 0
    models = []
    #cond_list = []
    for x in cond_list:#conditions us allow to block previously obtained models from appearing again. 
        s.add(x)
    while(s.check()==sat):
        models.append(s.model())
        #since z3 only gives one model on sat, we add the conditions to disallow already obtained models.
        #https://stackoverflow.com/questions/13395391/z3-finding-all-satisfying-models (top answer)
        o = Or(var_list[0]!=s.model()[var_list[0]],var_list[1]!=s.model()[var_list[1]])
        for i in range(2,len(var_list)):
            o = Or(o,var_list[i]!=s.model()[var_list[i]])
        cond_list.append(o)
        s.add(o)

    model_list = []
    for mode in models: # format the z3 model dictionaries for better traversing 
        s = model_formatter(mode, sat_r, sat_m, sat_h, sat_v)
        model_list.append(s)
    return [cond_list,model_list]# return all satisfying models and the conditions list (will be used to force new models)

#solve_step(R,mines, horizontals,verticals,None)

class tree_node:
    def __init__(self, model,parent):
        self.children =[]
        self.parent = parent
        self.model = model
        self.depth = -1
# model format followed = [R, mines,horizontals,verticals]

root = tree_node([R,mines,horizontals,verticals],None)
root.depth=0
result_trace = [] #will store all configurations leading to a solved board. 
switch = 0 #was used to abort all recursive calls if result was found (maybe not required now?)
bfs_queue = [] 
bfs_queue.append(root)

#generate bfs tree
def gen_tree(cond_list):
    global switch,moves
    if switch == 1 or len(bfs_queue)==0:
        return
    model = bfs_queue[0].model
    model_set = solve_step(model[0], model[1], model[2], model[3], cond_list) # get all possible moves.
    cond_list = model_set[0]
    bfs_queue[0].children = model_set[1]
    
    for x in bfs_queue[0].children:
        node = tree_node(x,bfs_queue[0])
        node.depth = node.parent.depth+1
        if(node.depth > moves):
            return
        c = combine(x)
        # for i in range(n):
        #     for j in range(n):
        #         print(c[i][j],end = " ")
        #     print()
        # print()
        for j in range(n):
            if x[0][j][n-1]==1: #since x is a satisfying model, x[0] is R (red car)
                         # if red car has reached the end, set the recursion abort switch,
                         # and trace the path till the initial input state .
                         # Note result_trace has elements in reverse order.
                switch = 1
                iter = node
                while (iter!=None):
                    result_trace.append(iter.model)
                    iter = iter.parent
                return
        bfs_queue.append(node)
    bfs_queue.pop(0)
    gen_tree(cond_list)

# check if root satisfies
root_sat = False
for j in range(n):
    if root.model[0][j][n-1]:
        root_sat=True

if root_sat!=True:

    cond_list = []
    gen_tree(cond_list)

    # print(len(result_trace))
    if (len(result_trace)==0 or len(result_trace)>moves+1):
        print("unsat")
    else:
        result_matrices = []
        for x in result_trace:
            c = combine(x)
            result_matrices.insert(0,c)
            # for i in range(n):
            #     for j in range(n):
            #         print(c[i][j],end = " ")
            #     print()
            # print()

        i_1,j_1,i_m1,j_m1 = 0,0,0,0

        for ind in range(len(result_matrices)-1):
            for i in range(n):
                for j in range(n):
                    if result_matrices[ind+1][i][j]-result_matrices[ind][i][j]==1:
                        i_1,j_1 = i,j
                    elif result_matrices[ind+1][i][j]-result_matrices[ind][i][j]==-1:
                        i_m1,j_m1 = i,j
            print(str((i_1+i_m1)//2)+','+str((j_1+j_m1)//2))