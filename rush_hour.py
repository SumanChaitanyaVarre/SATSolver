from z3 import *
import sys

r = unsat



#Functions
 
def or_array(array, size):
    if size == 1:
        return array[0]
    else:
        answer = Or (array[0], array[1])
        for i in range(2, size):
            answer = Or (answer, array[i])
        return answer

def and_array(array, size):
    if size == 1:
        return array[0]
    else:
        answer = And (array[0], array[1])
        for i in range(2, size):
            answer = And (answer, array[i])
        return answer


input = []
minecount = 0


with open(sys.argv[1]) as f:
	for line in f:
		input.append([int(v) for v in line.strip().split(',')])

for i in range(2, len(input)):
    if input[i][0] == 2:
        minecount += 1

carcount = len(input) - 2 - minecount
size = input[0][0] #grid size
max_limit = input[0][1] # max number of steps

if max_limit <= 10:
    limit = max_limit

elif size <= max_limit and max_limit < 50:
    if int(max_limit/2.5) > size :
        limit = max(int(max_limit/2.5), size)
    else:
        limit = max_limit

elif size <= max_limit and max_limit < 100:
    if int(max_limit/2.8) > size :
        limit = max(int(max_limit/2.8), size)
    else:
        limit = max_limit

elif max_limit >= 100:
    if int(max_limit/3) > size :
        limit = max(int(max_limit/3, size))
    else:
        limit = max_limit

else:
    limit = max_limit

# limit = max_limit
    
while(limit <= max_limit and r != sat):

    #Red Car
    red_pos_x = [ Int("red_pos_x_%s" % (i)) for i in range(limit+1) ] # red car x at step s
    red_pos_y = [ Int("red_pos_y_%s" % (i)) for i in range(limit+1) ] # red car y at step s
    red_pos_x[0] = input[1][0]
    red_pos_y[0] = input[1][1]

    orientation = [ Int("ori_%s" % (i)) for i in range(carcount) ]
    # orientation[car_no] = 0(vertical), 1(horizontal)


    #Normal Car
    nor_pos_x = [ [ Int("nor_pos_x_%s_%s" % (i, j)) for j in range(carcount) ] for i in range(limit+1) ] 
    # nor_pos_x[step][car_no] = x_cor

    nor_pos_y = [ [ Int("nor_pos_y_%s_%s" % (i, j)) for j in range(carcount) ] for i in range(limit+1) ] 
    # nor_pos_y[step][car_no] = y_cor

    #Red car movement at each step?
    red_move = [ Bool("red_move_%s" % (i)) for i in range(limit) ]	
    #which car moved at each step?
    move = [ [ Bool("move_%s_%s" % (i, j)) for j in range(carcount)] for i in range(limit)]


    #Is mine?
    ismine =  [ [ Int ("ism_%s_%s" % (i, j)) for j in range(size) ] for i in range(size) ]

    #Obstacles
    isempty = [ [ [Bool("ise_%s_%s_%s" % (i, j, k) ) for k in range(size)] for j in range(size)] for i in range(limit+1)]


    temp_ise = [ [ [False for k in range(size)] for j in range(size) ] for i in range(limit+1)]
    temp_ise[0][input[1][0]][input[1][1]] = True
    temp_ise[0][input[1][0]][input[1][1]+1] = True


    # for i in range(limit + 1):
    #     for j in range(size):
    #         for k in range(size):
    #             isempty[i][j][k] = True



    altered = [ [ [Int("altered_%s_%s_%s" % (i, j, k)) for k in range(2)] for j in range(2)] for i in range(limit) ]

    temp = 0
    for i in range(2, len(input)):
        if input[i][0] != 2:
            nor_pos_x[0][temp] = input[i][1]
            nor_pos_y[0][temp] = input[i][2]
            orientation[temp] = input[i][0]

            # isempty[0][input[i][1]][input[i][2]] = False
            temp_ise[0][input[i][1]][input[i][2]] = True

            if orientation[temp] == 1:
                # isempty[0][input[i][1]][input[i][2] + 1] = False
                temp_ise[0][input[i][1]][input[i][2] + 1] = True
            else:
                # isempty[0][input[i][1] + 1][input[i][2]] = False
                temp_ise[0][input[i][1] + 1][input[i][2]] = True
            temp += 1
        else:
            ismine[input[i][1]][input[i][2]] = True
            # isempty[0][input[i][1]][input[i][2]] = False
            temp_ise[0][input[i][1]][input[i][2]] = True

    solved = [ Bool ("solved_%s" % (i)) for i in range(limit+1) ] # completed at step = solved[i]?

    solver = Solver()
    solver.add(solved[limit])

    ##############
    for i in range(size):
        for j in range(size):
            solver.add( isempty[0][i][j] == Not(temp_ise[0][i][j]) )
    ############
    #Constarints


    for i in range(limit + 1):
        if i != limit:
            solver.add(Implies (solved[i], solved[i+1]))
        solver.add(And (red_pos_y[i] >= 0, red_pos_y[i] <= size - 2))
        solver.add(red_pos_x[i] == input[1][0])
        solver.add(And (red_pos_x[i] == input[1][0], red_pos_y[i] == size -2) == solved[i])

    #If mine or H Car present in same row as Red car --> Unsat
    for i in range(input[1][0] + 2, size):
        solver.add(Not(ismine[i][input[1][0]] == 1))


    # for i in range(limit):
    #     c = True
    #     for j in range(red_pos_x[i] + 2, size):
    #         c = And ( isempty[i][input[1][0]][j] ,c )
    #     solver.add(Implies( c, (
    #         red_move[i]
    #     )))

    # for i in range(limit):
    #     for j in range(size):
    #         for k in range(1, size-2):
    #             foo = []
    #             for l in range(k+1, size-2):
    #                 foo.append(isempty[i][j][l])


    #All cars in frame
    for i in range(limit + 1):
        solver.add(red_pos_x[i] == input[1][0])
        if (i < limit):

            solver.add(
                And(
                    altered[i][0][0] >= -1, altered[i][0][0] <= size-1, altered[i][1][0] >= -1, altered[i][1][0] <= size-1
                )
            )
            solver.add(
                And(
                    altered[i][0][1] >= -1, altered[i][0][1] <= size-1, altered[i][1][1] >= -1, altered[i][1][1] <= size-1
                )
            )


        for car_no in range(carcount): 
            if (orientation[car_no] == 0):
                solver.add(
                    And(
                        nor_pos_x[i][car_no] >= 0, nor_pos_x[i][car_no] <= size-2, nor_pos_y[i][car_no] >= 0, nor_pos_y[i][car_no] <= size-1
                    )
                )

            else:
                solver.add(
                    And(
                        nor_pos_x[i][car_no] >= 0, nor_pos_x[i][car_no] <= size-1, nor_pos_y[i][car_no] >= 0, nor_pos_y[i][car_no] <= size-2
                    )
                )


    for i in range(limit):
        temp = [(red_move[i])]
        for j in range(carcount):
            solver.add( Not(And(red_move[i], move[i][j])) )
            temp.append( move[i][j] )
            for k in range(j+1, carcount):
                solver.add( Not(And(move[i][j], move[i][k])) )
        solver.add( Implies(Not(solved[i]), or_array(temp, carcount+1)) )

    for i in range(limit):
        solver.add(red_pos_x[i+1] == red_pos_x[i])
        clause_1 = (red_pos_y[i+1] == red_pos_y[i] + 1)
        clause_2 = (red_pos_y[i+1] == red_pos_y[i] - 1)
        clause_0 = (red_pos_y[i+1] == red_pos_y[i])

        clause_3 = Or(clause_0, clause_1, clause_2)
        solver.add(clause_3)

        solver.add(Not(clause_0) == red_move[i])
        

        for j in range(size):
            a1 = And( (red_pos_y[i] == 0), (red_pos_x[i] == j) )
            a2 = And( (red_pos_y[i] == size - 2), (red_pos_x[i] == j) )

            solver.add(
                And(
                    Implies(a1, Not(clause_2)), Implies(a2, Not(clause_1)) 
                )
            )
            solver.add(
                And(
                    Implies(And(a1, clause_1), (isempty[i][j][2])), Implies(And(a1, clause_1), altered[i][0][0] == j), Implies(And(a1, clause_1), altered[i][0][1] == 0), Implies(And(a1, clause_1), altered[i][1][0] == j), Implies(And(a1, clause_1), altered[i][1][1] == 2), Implies(And(a2, clause_2), (isempty[i][j][size-3])), Implies(And(a2, clause_2), altered[i][0][0] == j), Implies(And(a2, clause_2), altered[i][0][1] == size-3), Implies(And(a2, clause_2), altered[i][1][0] == j), Implies(And(a2, clause_2), altered[i][1][1] == size-1)
                )
            )


            for k in range(1, size-2):
                # foo = []
                # for l in range(k+1, size):
                #     foo.append(isempty[i][j][l])
                # clause_4 = and_array(foo, len(foo))
                c = And((red_pos_x[i] == j), (red_pos_y[i] == k))

                # solver.add(Implies(And(c, clause_4), clause_1))

                solver.add(
                    And(
                        Implies(And(c, clause_1), isempty[i][j][k+2]), Implies(And(c, clause_1), altered[i][0][0] == j)
                    )
                )

                solver.add(
                    And(
                        Implies(And(c, clause_1), altered[i][0][1] == k), Implies(And(c, clause_1), altered[i][1][0] == j)
                    )
                )

                solver.add(
                    And(
                        Implies(And(c, clause_1), altered[i][1][1] == k+2), Implies(And(c, clause_2), (isempty[i][j][k-1]))
                    )
                )

                solver.add(
                    And(
                        Implies(And(c, clause_2), altered[i][0][0] == j), Implies(And(c, clause_2), altered[i][0][1] == k-1)
                    )
                )

                solver.add(
                    And(
                        Implies(And(c, clause_2), altered[i][1][0] == j), Implies(And(c, clause_2), altered[i][1][1] == k+1)
                    )
                )                

    for car_no in range(carcount):
        for i in range(limit):
            if (orientation[car_no] == 0):
                solver.add(nor_pos_y[i+1][car_no] == nor_pos_y[i][car_no])
                clause_1 = (nor_pos_x[i+1][car_no] == nor_pos_x[i][car_no] + 1)
                clause_2 = (nor_pos_x[i+1][car_no] == nor_pos_x[i][car_no] - 1)
                clause_0 = (nor_pos_x[i+1][car_no] == nor_pos_x[i][car_no])

                clause_3 = Or(clause_0, clause_1, clause_2)
                solver.add(clause_3)
                solver.add( Not(clause_0) == (move[i][car_no]) )
                for j in range(1, size-2):
                    for k in range(size):
                        
                        c = And((nor_pos_x[i][car_no] == j), (nor_pos_y[i][car_no] == k))
                        solver.add(
                            And(
                                Implies(And(c, clause_1), (isempty[i][j+2][k])), Implies(And(c, clause_1), altered[i][0][0] == j)
                            )
                        )
                        solver.add(
                            And(
                                Implies(And(c, clause_1), altered[i][0][1] == k), Implies(And(c, clause_1), altered[i][1][0] == j+2)
                            )
                        )
                        solver.add(
                            And(
                                Implies(And(c, clause_1), altered[i][1][1] == k), Implies(And(c, clause_2), (isempty[i][j-1][k]))
                            )
                        )
                        solver.add(
                            And(
                                Implies(And(c, clause_2), altered[i][0][0] == j-1), Implies(And(c, clause_2), altered[i][0][1] == k)
                            )
                        )
                        solver.add(
                            And(
                                Implies(And(c, clause_2), altered[i][1][0] == j+1), Implies(And(c, clause_2), altered[i][1][1] == k)
                            )
                        )
                for j in range(size):

                    a1 = And( (nor_pos_x[i][car_no] == 0), (nor_pos_y[i][car_no] == j) )
                    a2 = And( (nor_pos_x[i][car_no] == size-2), (nor_pos_y[i][car_no] == j) )
                    solver.add(
                        And(
                            Implies(a1, Not(clause_2)), Implies(a2, Not(clause_1))
                        )
                    )
                    solver.add(
                        And(
                            Implies(And(a1, clause_1), (isempty[i][2][j])), Implies(And(a1, clause_1), altered[i][0][0] == 0)
                        )
                    )
                    solver.add(
                        And(
                            Implies(And(a1, clause_1), altered[i][0][1] == j), Implies(And(a1, clause_1), altered[i][1][0] == 2)
                        )
                    )

                    solver.add(
                        And(
                            Implies(And(a1, clause_1), altered[i][1][1] == j) , Implies(And(a2, clause_2), (isempty[i][size-3][j]))
                        )
                    )

                    solver.add(
                        And(
                            Implies(And(a2, clause_2), altered[i][0][0] == size-3), Implies(And(a2, clause_2), altered[i][0][1] == j)
                        )
                    )
                    solver.add(
                        And(
                            Implies(And(a2, clause_2), altered[i][1][0] == size-1), Implies(And(a2, clause_2), altered[i][1][1] == j)
                        )
                    )
            else:
                solver.add(nor_pos_x[i+1][car_no] == nor_pos_x[i][car_no])
                clause_0 = (nor_pos_y[i+1][car_no] == nor_pos_y[i][car_no])
                clause_2 = (nor_pos_y[i+1][car_no] == nor_pos_y[i][car_no] - 1)
                clause_1 = (nor_pos_y[i+1][car_no] == nor_pos_y[i][car_no] + 1)
                clause_3 = Or(clause_0, clause_2, clause_1)
                solver.add( Not(clause_0) == (move[i][car_no]) )
                solver.add(clause_3)

                for k in range(size):
                    for j in range(1, size-2):

                        c = And((nor_pos_x[i][car_no] == k), (nor_pos_y[i][car_no] == j))
                        solver.add(
                            And(
                                Implies(And(c, clause_1), isempty[i][k][j+2]), Implies(And(c, clause_1), altered[i][0][0] == k) 
                            )
                        )
                        solver.add(
                            And(
                                Implies(And(c, clause_1), altered[i][0][1] == j), Implies(And(c, clause_1), altered[i][1][0] == k)
                            )
                        )
                        solver.add(
                            And(
                                Implies(And(c, clause_1), altered[i][1][1] == j+2), Implies(And(c, clause_2), (isempty[i][k][j-1]))
                            )
                        )
                        solver.add(
                            And(
                                Implies(And(c, clause_2), altered[i][0][0] == k), Implies(And(c, clause_2), altered[i][0][1] == j-1)
                            )
                        )

                        solver.add(
                            And(
                                Implies(And(c, clause_2), altered[i][1][0] == k), Implies(And(c, clause_2), altered[i][1][1] == j+1)
                            )
                        )

                for j in range(size):

                    a1 = And( (nor_pos_y[i][car_no] == 0), (nor_pos_x[i][car_no] == j) )
                    a2 = And( (nor_pos_y[i][car_no] == size-2), (nor_pos_x[i][car_no] == j) )
                    solver.add(
                        And(
                            Implies(a1, Not(clause_2)), Implies(a2, Not(clause_1))
                        )
                    )


                    solver.add(
                        And(
                            Implies(And(a1, clause_1), (isempty[i][j][2])), Implies(And(a1, clause_1), altered[i][0][0] == j), Implies(And(a1, clause_1), altered[i][0][1] == 0), Implies(And(a1, clause_1), altered[i][1][0] == j), Implies(And(a1, clause_1), altered[i][1][1] == 2), Implies(And(a2, clause_2), (isempty[i][j][size-3])), Implies(And(a2, clause_2), altered[i][0][0] == j), Implies(And(a2, clause_2), altered[i][0][1] == size-3), Implies(And(a2, clause_2), altered[i][1][0] == j), Implies(And(a2, clause_2), altered[i][1][1] == size-1)
                        )
                    )
                    
    for i in range(limit):
        solver.add( Implies(solved[i], And(altered[i][0][0] == -1, altered[i][0][1] == -1, altered[i][0][1] == -1, altered[i][0][1] == -1)) )
    for i in range(1, limit+1):
        for j in range(size):
            for k in range(size):
                cl1 = And(altered[i-1][0][0] == j, altered[i-1][0][1] == k)
                cl2 = And(altered[i-1][1][0] == j, altered[i-1][1][1] == k)
                solver.add( Or(cl1, cl2) == Not (Not (isempty[i][j][k]) == Not (isempty[i-1][j][k])) )

    r = solver.check()
    if solver.check() == sat:
        m = solver.model()
        for i in range(limit):
            if (m[solved[i]] == False):
                a = (int)(m[altered[i][0][0]].as_long())
                b = (int)(m[altered[i][0][1]].as_long())
                c = (int)(m[altered[i][1][0]].as_long())
                d = (int)(m[altered[i][1][1]].as_long())
                print( str((int)((a+c)/2)) + ", " + str((int)((b+d)/2)))

    # limit = int(limit*2)
    if limit == max_limit:
        limit = max_limit+1
    # elif limit >= max_limit:
    #     limit = max_limit
    else:
        limit = max_limit

if r == unsat:
    print("unsat")