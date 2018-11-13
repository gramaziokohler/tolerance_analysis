from compas.datastructures.network import Network
from compas_fab.fab.geometry import Frame, Transformation, Rotation, Translation
from compas.geometry.elements import Line
from compas.geometry import distance_point_point
from collections import deque
import random as r
from graphviz import Digraph
from heap import Heap
import random
import operator
import itertools

r.seed(1)

__author__     = 'Augusto Gandia, Gonzalo Casas'
__copyright__  = 'Copyright 2018, Gramazio Kohler Research - ETH Zurich'
__license__    = 'MIT'
__email__      = 'gandia@arch.ethz.ch'

def setup(rawData):
        #Create and return sorted data in list
        cities = list()
        data = list()

        for line in rawData:
            item = list()
            temp = line.split()
            item.extend([temp[0],temp[1],int(temp[2])])
            cities.extend([temp[0],temp[1]])
            data.append(item)
        return sorted(data, key=operator.itemgetter(2)),sorted(set(cities))
        
def depth_first_tree(adjacency, root):
    """Construct a spanning tree using a depth-first search.
    Parameters
    ----------
    adjacency : dict
        An adjacency dictionary.
    root : hashable
        The identifier of the root node.
    Returns
    -------
    list
        List of nodes in depth-first order.
    dict
        Dictionary of predecessors for each of the nodes.
    list
        The depth-first paths.
    """
    adjacency = {key: set(nbrs) for key, nbrs in iter(adjacency.items())}
    tovisit = [root]
    visited = set()
    ordering = []
    predecessors = {}
    paths = [[root]]
    #if there are nodes in tovisit
    while tovisit:
        # pop the last added element from the stack
        node = tovisit.pop()
        if node not in visited:
            # add node to last path
            paths[-1].append(node)
            # mark the node as visited
            visited.add(node)
            ordering.append(node)
            # add the unvisited nbrs to the stack
            nodes = adjacency [node] - visited
            # if there still not visited nbrs
            if nodes:
                for child in nodes:
                    predecessors[child] = node
            else:
                paths.append([])
            tovisit.extend(nodes)
    if not len(paths[-1]):
        del paths[-1]
    return ordering, predecessors, paths

def breadth_first_tree(adjacency, root):
    tovisit  = deque([root])
    visited  = set([root])
    ordering = [root]
    predecessors = {}
    paths = []
    while tovisit: 
        node = tovisit.popleft()
        for nbr in adjacency[node]:
            if nbr not in visited:
                predecessors[nbr]=node
                tovisit.append(nbr)
                visited.add(nbr)
                ordering.append(nbr)
        else:
            path = [node]
            while path[-1] in predecessors:
                path.append(predecessors[path[-1]])
            paths.append(list(reversed(path)))
    return ordering, predecessors, paths

def network_bfs_paths(adjacency, root, goal):
    """Return all paths from root to goal.
    Due to the nature of the search, the first path returned is the shortest.
    """
    adjacency = dict((key, set(nbrs)) for key, nbrs in adjacency.iteritems())
    tovisit = deque([(root, [root])])
    while tovisit:
        node, path = tovisit.popleft()
        for nbr in adjacency[node] - set(path):
            if nbr == goal:
                yield path + [nbr]
            else:
                tovisit.append((nbr, path + [nbr]))

def network_shortest_path(adjacency, root, goal):
    try:
        return next(network_bfs_paths(adjacency, root, goal))
    except StopIteration:
        return None

def init(E):
    nodes = {}
    for e in E:
        nodes[e] = None
    return nodes

def find(nodes, U):
    if U not in nodes:
        print('Find failed: ' + str(U) + ' not found')
        return None
    if nodes[U] == None:
        return U
    return find(nodes,nodes[U])

def union(nodes,U0,U1):
    U1_temp = find(nodes,U1)
    U0_temp = find(nodes,U0)
    if U1_temp == None or U0_temp == None:
        failed = []
        if U0_temp == None:
            failed.append(U0)
        if U1_temp == None:
            failed.append(U1)
        print('\nUnion failed: Element(s) ' + str(failed) + ' not found\n')
        return None
    if U0_temp != U1_temp:
        nodes[U0_temp] = U1_temp
    return U1_temp

def check_connectivity(current_beam, adjacency, beams_geometry, result):
    
    
    #Type of beam (0 = bottom beams, 1 = boundary beams, 2 = infills)
    beams_type={0:2 ,   1:1 ,   2:1 ,   3:1 ,   4:1 ,   5:1 ,   6:1 ,   7:1 ,   8:1 ,   9:1 ,
                10:1 ,  11:1 ,  12:1 ,  13:2 ,  14:2 ,  15:2 ,  16:2 ,  17:2 ,  18:2 ,  19:2 ,
                20:2 ,  21:2 ,  22:2 ,  23:2 ,  24:2 ,  25:2 ,  26:2 ,  27:2 ,  28:2 ,  29:2 ,
                30:2 ,  31:2 ,  32:1 ,  33:1 ,  34:2 ,  35:2 ,  36:2 ,  37:1 ,  38:2 ,  39:2 ,
                40:2 ,  41:2 ,  42:2 ,  43:2 ,  44:2 ,  45:2 ,  46:2 ,  47:2 ,  48:2 ,  49:2 ,
                50:2 ,  51:2 ,  52:2 ,  53:2 ,  54:2 ,  55:0 ,  56:0 ,  57:2 ,  58:2 , 59:0 ,
                60:2 ,  61:2 ,  62:2 ,  63:2 ,  64:2 ,  65:2 ,  66:2 ,  67:2 ,  68:2 ,  69:2 ,
                70:2 ,  71:2 ,  72:2 ,  73:2 ,  74:2 ,  75:2 ,  76:0 ,  77:0 ,  78:2 ,  79:2 ,
                80:0 ,  81:2 ,  82:2 ,  83:2 ,  84:2 ,  85:2 ,  86:2 ,  87:2 ,  88:2 ,  89:2 ,
                90:2 ,  91:2 ,  92:2 ,  93:2 ,  94:2 ,  95:2 ,  96:2 ,  97:0 ,  98:0 ,  99:2 ,
                100:2 , 101:0 , 102:2 , 103:2 , 104:2 , 105:2 , 106:2 , 107:2 , 108:2 , 109:2 ,
                110:2 , 111:2 , 112:2 , 113:2 , 114:2 , 115:2 , 116:2 , 117:2 , 118:0 , 119:0 ,
                120:2 , 121:2 , 122:0 , 123:2 , 124:2 , 125:2 , 126:2 , 127:2 , 128:2 , 129:2 ,
                130:2 , 131:2 , 132:2 , 133:2 , 134:2 , 135:2 , 136:2 , 137:2 , 138:2 , 139:0 ,
                140:0 , 141:2 , 142:2 , 143:0 , 144:2 , 145:2 , 146:2 , 147:2 , 148:2 , 149:2 ,
                150:2 , 151:2 , 152:2 , 153:2 , 154:2 , 155:2 , 156:2 , 157:2 , 158:2 , 159:2 ,
                160:0 , 161:0 , 162:2 , 163:2 , 164:0 , 165:2 , 166:2 , 167:2 , 168:2 , 169:2 ,
                170:2 , 171:2 , 172:2 , 173:2 , 174:2 , 175:2 , 176:2 , 177:2 , 178:2 , 179:2 ,
                180:2 , 181:2 , 182:2 , 183:2 , 184:2 , 185:1 , 186:1 , 187:1 , 188:1 , 189:1 ,
                190:1 , 191:1 , 192:1 , 193:1 , 194:1 , 195:1 , 196:1 , 197:1 , 198:1 , 199:1 ,
                200:2 , 201:2 , 202:2 , 203:2 , 204:2 , 205:2 , 206:2 , 207:2 , 208:2 , 209:2 ,
                210:2 , 211:2 , 212:2 , 213:2 , 214:2 , 215:2 , 216:2 , 217:2 , 218:2 , 219:2 ,
                220:2 , 221:2 , 222:2 , 223:2 , 224:2 , 225:2 , 226:2 , 227:2 , 228:2 , 229:2 ,
                230:2 , 231:1 , 232:2 , 233:2 , 234:1 , 235:2 , 236:1 , 237:1 , 238:1 , 239:2 ,
                240:2 , 241:2 , 242:2 , 243:2 , 244:2 , 245:2 , 246:2 , 247:2 , 248:2 , 249:2 ,
                250:2 , 251:2 , 252:2 , 253:2 , 254:2 , 255:2 , 256:2 , 257:2 , 258:2 , 259:2 ,
                260:2 , 261:2 , 262:2 , 263:2 , 264:2 , 265:2 , 266:2 , 267:2 , 268:1 , 269:1 ,
                270:2 , 271:2 , 272:1 , 273:1 , 274:1 , 275:1 , 276:2 , 277:2 , 278:2 , 279:2 ,
                280:2 , 281:2 , 282:2 , 283:2 , 284:2 , 285:2 , 286:2 , 287:2 , 288:2 , 289:2 ,
                290:2 , 291:2 , 292:2 , 293:2 , 294:2 , 295:2 , 296:2 , 297:2 , 298:2 , 299:2 ,
                300:2 , 301:2 , 302:2 , 303:2 , 304:2 , 305:2 , 306:1 , 307:1 , 308:2 , 309:2 ,
                310:1 , 311:1 , 312:1 , 313:1 , 314:2 , 315:2 , 316:2 , 317:2 , 318:2 , 319:2 ,
                320:2 , 321:2 , 322:2 , 323:2 , 324:2 , 325:2 , 326:2 , 327:2 , 328:2 , 329:2 ,
                330:2 , 331:2 , 332:2 , 333:2 , 334:2 , 335:2 , 336:2 , 337:2 , 338:2 , 339:2 ,
                340:2 , 341:2 , 342:2 , 343:2 , 344:1 , 345:1 , 346:2 , 347:2 , 348:1 , 349:1 ,
                350:1 , 351:1 , 352:2 , 353:2 , 354:2 , 355:2 , 356:2 , 357:2 , 358:2 , 359:2 ,
                360:2 , 361:2 , 362:2 , 363:2 , 364:2 , 365:2 , 366:2 , 367:2 , 368:2 , 369:2 ,
                370:2 , 371:2 , 372:2 , 373:2 , 374:2 , 375:2 , 376:2 , 377:2 , 378:2 , 379:2 ,
                380:1 , 381:1 , 382:2 , 383:1 , 384:1 , 385:1 , 386:1 , 387:1 , 388:0 , 389:2 ,
                390:0 , 391:0 , 392:0 , 393:0 , 394:0 , 395:0 , 396:0 , 397:0 , 398:0 , 399:0 ,
                400:0 , 401:0 , 402:0 , 403:2 , 404:0 , 405:0 , 406:1 , 407:1 , 408:1 , 409:1 ,
                410:0 , 411:0 , 412:0 , 413:0 , 414:0 , 415:2 , 416:2 , 417:2 , 418:2 , 419:2 ,
                420:2 , 421:2 , 422:2 , 423:2 , 424:2 , 425:0 , 426:0 , 427:0 , 428:2 , 429:2 ,
                430:2 , 431:2 , 432:2 , 433:2 , 434:2 , 435:2 , 436:2 , 437:2 , 438:0 , 439:0 ,
                440:0 , 441:2 , 442:2 , 443:2 , 444:2 , 445:2 , 446:2 , 447:2 , 448:2 , 449:2 ,
                450:2 , 451:0 , 452:0 , 453:0 , 454:0 , 455:0 , 456:0 , 457:0 , 458:0 , 459:0 ,
                460:2 , 461:2 , 462:2 , 463:2 , 464:2 , 465:2 , 466:2 , 467:2 , 468:2 , 469:2 ,
                470:2 , 471:2 , 472:2 , 473:2 , 474:2 , 475:2 , 476:2 , 477:2 , 478:2 , 479:2 ,
                480:2 , 481:2 , 482:2 , 483:2 , 484:0 , 485:0 , 486:0 , 487:2 , 488:2 , 489:2 ,
                490:2 , 491:2 , 492:2 , 493:2 , 494:2 , 495:2 , 496:2 , 497:0 , 498:0 , 499:0 ,
                500:2 , 501:2 , 502:2 , 503:2 , 504:2 , 505:2 , 506:2 , 507:2 , 508:2 , 509:2 ,
                510:2 , 511:1 , 512:1 , 513:0 , 514:2 , 515:2 , 516:2 , 517:2 , 518:2 , 519:2 ,
                520:2 , 521:2 , 522:2 , 523:2 , 524:2 , 525:2 , 526:2 , 527:2 , 528:1 , 529:1 ,
                530:1 , 531:1 , 532:1 , 533:1 , 534:0 , 535:0 , 536:0 , 537:0 , 538:0 , 539:0 ,
                540:2 , 541:2 , 542:2 , 543:2 , 544:2 , 545:2 , 546:2 , 547:1 , 548:1 , 549:2 ,
                550:1 , 551:2 , 552:2 , 553:2 , 554:2 , 555:2 , 556:2 , 557:2 , 558:2 , 559:1 ,
                560:1 , 561:2 , 562:2 , 563:1 , 564:1 , 565:1 , 566:1 , 567:1 , 568:1 , 569:1 ,
                570:1 , 571:1 , 572:1 , 573:2 , 574:1 , 575:1 , 576:2 , 577:2 , 578:2 , 579:2 ,
                580:2 , 581:2 , 582:2 , 583:2 , 584:0 , 585:0 , 586:0 , 587:0 , 588:2 , 589:2 ,
                590:2 , 591:2 , 592:2 , 593:2 , 594:2 , 595:2 , 596:2 , 597:1 , 598:0 , 599:0,
                600:0 , 601:0 , 602:0 , 603:1 , 604:1 , 605:1 , 606:2 , 607:2 , 608:2 , 609:2 ,
                610:2 , 611:2 , 612:2 , 613:2 , 614:2 , 615:2 , 616:2 , 617:2 , 618:1 , 619:2 ,
                620:2 , 621:2 , 622:2 , 623:2 , 624:2 , 625:2 , 626:2 , 627:2 , 628:2 , 629:1,
                630:1 ,631:1}

     
    check=False
    nbrs=set(adjacency[current_beam])
    print nbrs
    #if bottom beam
    if beams_type[current_beam]==0:
        check=True


    #if boundary beam
    if beams_type[current_beam]==1:
        #iter nbrs
        check=True
    #if infill
    if beams_type[current_beam]==2:
        check=True
    
    """
    nbrs=set(adjacency[current_beam])
    #(0 = bottom chord) if beam is bottom chord it is fabricatable by default
    if beams_type[current_beam]==0:
        check=True

    #(1 = top chord) if beam is top cord check that at least four vertical neighbours are there
    if beams_type[current_beam]==1:
        #iter nbrs
        counter=0
        for nbr_node in set(nbrs):
            nbr_node_type=beams_type[nbr_node]
            #if nbr is vertical or diagonal
            if nbr_node_type==2:
                #check if any verticals or diagonal already assembled
                if str(nbr_node) in result:
                    counter=counter+1
        if counter>1:#it is considered to be stable if there is at least two supports
            check=True

    #(2 = verticals) if beam is vertical or diagonal check that at least one bottom_cord neighbour is assembled
    if beams_type[current_beam]==2:
        #iter nbrs
        for nbr_node in nbrs: 
            nbr_node_type=beams_type[nbr_node]
            #if nbr is bottom_cord 
            if nbr_node_type==0:
                #check if any bottom_cord already assembled
                if str(nbr_node) in result:
                    check=True

    #(3 = wall rafter) if beam is wall rafter
    if beams_type[current_beam]==3:
        #iter nbrs
        counter=0
        for nbr_node in nbrs:
            nbr_node_type=beams_type[nbr_node]
            #if nbr is bottom or top cord 
            if nbr_node_type==0 or nbr_node_type==1:
                #if already assembled
                if str(nbr_node) in result:
                    counter=counter+1
        if counter>1:
            check=True

    #(4 = slab rafter) if beam is slab rafter
    #To be true it needs to be connected to one top cord = 1 or to two slab rafter = 4
    if beams_type[current_beam]==4:
        #iter nbrs
        counter=0
        for nbr_node in nbrs:
            nbr_node_type=beams_type[nbr_node]
            #if nbr is top cord 
            if nbr_node_type==1:
                #if already assembled
                if str(nbr_node) in result:
                    counter=counter+2
            #if nbr is top cord
            if nbr_node_type==4:
                if str(nbr_node) in result:
                    counter=counter+1
        if counter>1:
            check=True

    #(3 = wall rafter) if beam is wall rafter
    if beams_type[current_beam]==5:
        #iter nbrs
        counter=0
        for nbr_node in nbrs:
            nbr_node_type=beams_type[nbr_node]
            #if nbr is bottom or top cord 
            if nbr_node_type==0 or nbr_node_type==2:
                #if already assembled
                if str(nbr_node) in result:
                    counter=counter+1
        if counter>1:
            check=True
    """
    return check

# Method to perform Kruskal's Algorithm    
def kruskal(data,nodes,adjacency_dictionary,beams_geometry):#data no, nodes ok, adjacency_dictionary no , beams_geometry ok
    distance = 0
    result = list()
    nodes = init(nodes)
    forward_counters={}
    beams_propagation_path={}
    stored_goal=[]
    predecessors=[]

    escape = 0
    while len(data):
        escape += 1
        if escape > 3000:
            raise Exception("Everything went to hell")
        weighted_edge = data.pop(0)
        if find(nodes,weighted_edge[0]) != find(nodes,weighted_edge[1]):
            can_connect_beam_1 = check_connectivity(int(weighted_edge[0]), adjacency_dictionary, beams_geometry, result)
            can_connect_beam_2 = check_connectivity(int(weighted_edge[1]), adjacency_dictionary, beams_geometry, result)
            """
            if not can_connect_beam_1 or not can_connect_beam_2:
            
                key = '%s-%s' % (weighted_edge[0], weighted_edge[1])
                if key in forward_counters:
                    forward_counters[key] += 1
                else:
                    forward_counters[key] = 1
                forward_count=forward_counters[key]
                data.insert(forward_count, weighted_edge)
                continue
            """
            forward_counters = {}
            union(nodes, weighted_edge[0],weighted_edge[1])
            beam_1=weighted_edge[0]
            beam_2=weighted_edge[1]
            result.append(beam_1)
            result.append(beam_2)
            seen = set()
            cleaned_result=[x for x in result if not (x in seen or seen.add(x))]
            """
            #Build an adjacency dictionary for each assembly step
            beams_parent={}
            #Iterate already assembled beams
            for assembled_beam in cleaned_result:
                #Get current beam nbrs
                beam_nbrs=adjacency_dictionary[int(assembled_beam)]
                #Check if any assembled beam is neighbour of current beam
                for beam in cleaned_result:
                    if int(beam) in beam_nbrs:
                        #if key exists
                        if int(assembled_beam) not in beams_parent:
                            beams_parent.update({int(assembled_beam):[int(beam)]})
            """
            """
            #Store parent of each beam according to fabrication sequence
            #Remove duplicates from result
            seen = set()
            cleaned_result=[x for x in result if not (x in seen or seen.add(x))]
            #Build an adjacency dictionary for each assembly step
            beams_parent={}
            #Iterate already assembled beams
            for assembled_beam in cleaned_result:
                #Get current beam nbrs
                beam_nbrs=adjacency_dictionary[int(assembled_beam)]
                #Check if any assembled beam is neighbour of current beam
                for beam in cleaned_result:
                    if int(beam) in beam_nbrs:
                        #if key exists
                        if int(assembled_beam) not in beams_parent:
                            beams_parent.update({int(assembled_beam):[int(beam)]})
    """
    return cleaned_result

def midpoint_point_point(a, b):
    return [0.5 * (a[0] + b[0]),
            0.5 * (a[1] + b[1]),
            0.5 * (a[2] + b[2])]

def midpoint_line(line):
    return midpoint_point_point(*line)
    
def vertex_neighbours(self,key):
    """Return the neighbours of a vertex."""
    return list(self.halfedge[key])

def edge_connected_edges(self, u, v):
        edges = []
        for nbr in vertex_neighbours(self,u):
            if nbr in self.edge[u]:
                edges.append((u, nbr))
            else:
                edges.append((nbr, u))
        for nbr in vertex_neighbours(self,v):
            if nbr in self.edge[v]:
                edges.append((v, nbr))
            else:
                edges.append((nbr, v))
        return edges

def delete_vertex(self, key): #This could be removed in newer versions of compas
    for nbr in self.vertex_neighbours(key):
        del self.halfedge[key][nbr]
        del self.halfedge[nbr][key]
        if key in self.edge and nbr in self.edge[key]:
            del self.edge[key][nbr]
        else:
            del self.edge[nbr][key]
    del self.vertex[key]
    del self.halfedge[key]
    del self.edge[key]

def translate_frame_own_xyz(transformation,x_dist, y_dist, z_dist):
    x_transform = [[1, 0, 0, (transformation[0, 0] * x_dist)],
                   [0, 1, 0, (transformation[1, 0] * x_dist)],
                   [0, 0, 1, (transformation[2, 0] * x_dist)],
                   [0, 0, 0, 1]]
    y_transform = [[1, 0, 0, (transformation[0, 1]*y_dist)],
                   [0, 1, 0, (transformation[1, 1]*y_dist)],
                   [0, 0, 1, (transformation[2, 1]*y_dist)],
                   [0, 0, 0, 1]]
    z_transform = [[1, 0, 0, (transformation[0, 2]*z_dist)],
                   [0, 1, 0, (transformation[1, 2]*z_dist)],
                   [0, 0, 1, (transformation[2, 2]*z_dist)],
                   [0, 0, 0, 0]]
    return Translation.from_matrix(z_transform)*Translation.from_matrix(y_transform)*Translation.from_matrix(x_transform)

def add_tolerance(frame,dist_x,dist_y,dist_z):
    origin_V0=Transformation.from_frame(frame)
    tolerance=translate_frame_own_xyz(origin_V0, dist_x,dist_y,dist_z)
    M1=tolerance*origin_V0
    return Frame.from_transformation(M1)

class ToleranceNetwork(Network):
    #General Network required to 1) generate assembly sequence to 2) perform tolerance analysis
    def __init__(self, joint_edges, beam_edges, ordered_beams, weights_list):
        super(ToleranceNetwork, self).__init__() 
        input_dict = {'joint_edges': joint_edges, 'beam_edges': beam_edges, 'ordered_beams': ordered_beams}
        self.attributes.update(input_dict)
        self.build_geometry_network()
        self.build_topology_network (weights_list)
        self.assembly_sequence_search()
        #self.run_tolerance_analysis()
        #self.assembly_sequence_draw()

    def build_geometry_network(self):
        #add vertices of beam_edges to Tolerance Network(vertices same as Geometry network)
        #iterate beam_edges indexes
        for index in range(len(self.attributes ['beam_edges'])):
            #get vertex coordinates 
            position = self.attributes['beam_edges'][index][0]
            #generate vertex u, add coordinates and vertex type as attribute
            u=self.add_vertex(attr_dict={'x': position[0], 'y' : position[1], 'z' : position[2], 'vertex_type': 'member'})
            #get vertex coordinates 
            position = self.attributes ['beam_edges'][index][1]
            #generate vertex v, add coordinates and vertex type as attribute
            v=self.add_vertex(attr_dict={'x': position[0], 'y' : position[1], 'z' : position[2], 'vertex_type': 'member'})
            #add beam edge, beam object, edge_type, u_coordinate , v_coordinate
            self.add_edge(u,v, {'edge_type': 'member','beam': self.attributes ['ordered_beams'][index], 'u_coordinate':self.vertex_coordinates(u), 'v_coordinate': self.vertex_coordinates(v), 'member_edge_nbrs': []})

        # BUILD GEOMETRY NETWORK
        #compare joint edges and beam edges
        store_joint_new_u=[]
        store_joint_new_v=[]
        #Iterate joint edges
        for index in range (len(self.attributes['joint_edges'])):
            #get joint_vertices coordinates
            joint_u_coordinate=self.attributes ['joint_edges'][index][0] 
            joint_v_coordinate=self.attributes ['joint_edges'][index][1]
            #Iterate beam edges
            corresponding_joint_u_index=None #this can be revised
            corresponding_joint_v_index=None
            for u,v,attr in self.edges(data=True):
                #Get beam_vertices coordinates
                beam_u_coordinate=attr['u_coordinate']
                beam_v_coordinate=attr['v_coordinate']
                #Compare joint vertex u and beam vertex u
                if distance_point_point(joint_u_coordinate,beam_u_coordinate) < 0.5:
                    global corresponding_joint_u_index
                    corresponding_joint_u_index=u
                #Compare joint vertex u and beam vertex v
                elif distance_point_point(joint_u_coordinate,beam_v_coordinate) < 0.5:
                    global corresponding_joint_u_index
                    corresponding_joint_u_index=v
                #Compare joint vertex v and beam vertex u
                elif distance_point_point(joint_v_coordinate,beam_u_coordinate) < 0.5:
                    global corresponding_joint_v_index
                    corresponding_joint_v_index=u
                #Compare joint vertex v and beam vertex v
                elif distance_point_point(joint_v_coordinate,beam_v_coordinate) < 0.5:
                    global corresponding_joint_v_index
                    corresponding_joint_v_index=v
            #Store corresponding joint v index
            store_joint_new_u.append(corresponding_joint_u_index)
            #Store corresponding joint u index
            store_joint_new_v.append(corresponding_joint_v_index)
        for index in range(len(store_joint_new_v)):
            self.add_edge(store_joint_new_u[index], store_joint_new_v[index], {'edge_type': 'joint', 'beam': None})
        #STORE CONNECTIVITY IN EDGE MEMBERS
        #Iter joints and check connected edges        
        for u,v,attr in self.edges(data=True):
            if attr['edge_type']=='joint':
                connected_joint_edges_list=edge_connected_edges(self,u,v) #per beam edge a list of connected joint edges
                connected_member_edges=[]                
                #iter connected edges
                for joint_edge in connected_joint_edges_list:
                    #if connected is member
                    if self.get_edge_attribute(joint_edge[0],joint_edge[1],'edge_type')=='member':
                        #store it
                        connected_member_edges.append((joint_edge[0],joint_edge[1])) 
                
                first_member_edge_neighbours=self.get_edge_attribute(connected_member_edges[0][0],connected_member_edges[0][1],'member_edge_nbrs')
                #(by appending them they get included in the attribute)
                first_member_edge_neighbours.append(connected_member_edges[1]) 
                #get existing neighbours from second edge 
                sec_member_edge_neighbours=self.get_edge_attribute(connected_member_edges[1][0],connected_member_edges[1][1],'member_edge_nbrs')
                #(by appending them they get included in the attribute)
                sec_member_edge_neighbours.append(connected_member_edges[0])
        
    # GENERATE ASSEMBLY SEQUENCE NETWORK (beams=nodes and connections=edges)
    def build_topology_network(self, weights_list):
        beams_geometry=self.attributes['ordered_beams']
        #this "topology network" is an inversion of the "geometry_network" by turning beams into vertices
        self.assembly_sequence_network=Topology_Network(self, weights_list, beams_geometry)

    def assembly_sequence_search(self):
        #Adjacency dictionary for COMPAS deph_first_tree
        adjacency_dictionary=self.assembly_sequence_network.adjacency_dictionary
        beams_geometry=self.assembly_sequence_network.beams_geometry
        #Create a list that represents the relations for a directed graph
        #List with weighted edges (a, b, c) a=start vertex b=end vertex c=weight
        directed_edges=[]
        #Iterate nodes
        for node in adjacency_dictionary:
            parent_weight = self.assembly_sequence_network.get_vertex_attribute(node, 'weight')
            #Iterate neighbours of each node
            for nbr in adjacency_dictionary[node]:
                child_weight = self.assembly_sequence_network.get_vertex_attribute(nbr, 'weight') 
                parent = [str(nbr), str(node), parent_weight]
                child = [str(node), str(nbr), child_weight]
                if parent_weight > child_weight:
                    directed_edges.append(parent)
                    if child in directed_edges:
                        directed_edges.remove(child)
                else:
                    directed_edges.append(child)
                    if parent in directed_edges:
                        directed_edges.remove(parent)
        sorted_directed_edges = sorted(directed_edges, key=operator.itemgetter(2))
        self.sorted_directed_edges = sorted_directed_edges[:]
        nodes = map(str, self.assembly_sequence_network.vertices())
        result = kruskal(sorted_directed_edges,nodes,adjacency_dictionary,beams_geometry)
        self.result=result
        #self.beams_parent=beams_parent


    def run_tolerance_analysis(self):

        """
        Geometry network (member and joint members)

        attr=
        'member_edge_nbrs':[(8, 9), (32, 33)], 
        'connection_frames', 
        'u_coordinate', 'v_coordinate',
        'edge_type': 'member' or 'joint', 
        'beam'

        Example:
        for u,v,attr in self.edges(data=True):
            print "Geometry Network u,v,att", u,v,attr
        
        Topology network (member as vertex)

        attr=
        'x','y','z', 
        'connected_vertices':[0, 2], 
        'weight': 2

        Example:
        for u,attr in self.topology_network.vertices(data=True):
            print "Topology Network u,v,att", u,v,attr

        Mapping:
        Geometry network (edge_u,edge_v) to Topology Network (vertex)
        vertex (Beam) = edge_u/2 (Connection)

        Beam of Topology Network (vertex) to Beam of Geometry network
        edge_u=vertex*2
        edge_v=(vertex*2)+1
        """
        result=self.result
        #beams_parent=self.beams_parent

        #1)Add Frames to Geometry Network
        for u,v,attr in self.edges(data=True):
            if attr['edge_type']=='member':
                #Rhino Plane
                end_plane_u=attr['beam'].end_planes[0]
                end_plane_v=attr['beam'].end_planes[1]
                #end_plane_u.Rotate(3.14, end_plane_u[2])
                #Compas Frame
                frame_u=Frame(end_plane_u[0], end_plane_u[1], end_plane_u[2])
                frame_v=Frame(end_plane_v[0], end_plane_v[1], end_plane_v[2])
                #Set Compas Frame as attribute
                #self.set_edge_attribute(u,v,'connection_frames', (frame_u, frame_v))
                self.set_vertex_attribute(u, 'connection_frame', frame_u)
                self.set_vertex_attribute(v, 'connection_frame', frame_v)
        
        #TOLERANCE PPROPAGATION ORDER AND DIRECTION

        #Get beam from assembly sequence
        current_beam_index_TN=int(result[2])
        #Get beam parent (TN)
        parent_beam_index_TN=beams_parent[current_beam_index_TN][0]

        #Search vertices of joint shared with parent
        #Get beam vertices (GN)
        beam_u_GN=current_beam_index_TN*2
        beam_v_GN=current_beam_index_TN*2+1
        #Get parent beam vertices (GN)
        parent_beam_u_GN=parent_beam_index_TN*2
        parent_beam_v_GN=parent_beam_index_TN*2+1
        #Dictionary key: TopologyNetwork beam index (int) value: Geometry Network joint vertices indices from child to parent
        child_to_parent_joint=[]
        for u,v,attr in self.edges(data=True):
            if attr['edge_type']=='joint':
                #print "joint",u,v
                if (beam_u_GN,parent_beam_u_GN)==(u,v):
                    child_to_parent_joint.append(u)
                    child_to_parent_joint.append(v)
                elif (beam_u_GN,parent_beam_u_GN)==(v,u):
                    child_to_parent_joint.append(v)
                    child_to_parent_joint.append(u)
                elif (beam_u_GN,parent_beam_v_GN)==(u,v):
                    child_to_parent_joint.append(u)
                    child_to_parent_joint.append(v)
                elif (beam_u_GN,parent_beam_v_GN)==(v,u):
                    child_to_parent_joint.append(v)
                    child_to_parent_joint.append(u)
                elif (beam_v_GN,parent_beam_u_GN)==(u,v):
                    child_to_parent_joint.append(u)
                    child_to_parent_joint.append(v)
                elif (beam_v_GN,parent_beam_u_GN)==(v,u):
                    child_to_parent_joint.append(v)
                    child_to_parent_joint.append(u)
                elif (beam_v_GN,parent_beam_v_GN)==(u,v):
                    child_to_parent_joint.append(u)
                    child_to_parent_joint.append(v)
                elif (beam_v_GN,parent_beam_v_GN)==(v,u):
                    child_to_parent_joint.append(v)
                    child_to_parent_joint.append(u)
        
        # joint vertices indices (GN)

        parent_joint_vertex_index=child_to_parent_joint[1] #31
        child_joint_vertex_index=child_to_parent_joint[0] #0
        if parent_joint_vertex_index == parent_beam_u_GN:
            parent_other_vertex_index=parent_beam_v_GN
        else:
            parent_other_vertex_index=parent_beam_u_GN
        if child_joint_vertex_index == beam_u_GN: 
            child_other_vertex_index=beam_v_GN
        else:
            child_other_vertex_index=beam_u_GN

        # joint frames
        parent_joint_frame=self.get_vertex_attribute(parent_joint_vertex_index, 'connection_frame')
        parent_other_frame=self.get_vertex_attribute(parent_other_vertex_index, 'connection_frame')
        child_joint_frame=self.get_vertex_attribute(child_joint_vertex_index, 'connection_frame')
        child_other_frame=self.get_vertex_attribute(child_other_vertex_index, 'connection_frame')

        transformations=[]
        #Transformation to V0 (beam 1)
        V_V0=Transformation.from_frame(parent_other_frame)
        transformations.append(V_V0)
        
        #Transformation to V1 (beam 1)
        V0_V1=Transformation.from_frame_to_frame(parent_other_frame, parent_joint_frame)
        transformations.append(V0_V1*V_V0)

        #Transformation to V2 (joint 1)
        V1_V2=Transformation.from_frame_to_frame(parent_joint_frame,add_tolerance(child_joint_frame,0,0,100))
        transformations.append(V1_V2*V0_V1*V_V0)

        #Transformation to V3 (beam 2)
        V2_V3=Transformation.from_frame_to_frame(child_joint_frame, child_other_frame)
        transformations.append(V1_V2*V2_V3*V0_V1*V_V0)

        self.transformations=transformations

    def assembly_sequence_draw(self):
        result=self.result
        weighted_edges=self.sorted_directed_edges
        #color convention
        color="/rdbu8/"
        #setup
        directed_graph=Digraph(format='png')
        directed_graph.attr(ranksep='7', resolution='80', lheight='1000', lwidth='2000', smoothing='true')#, bgcolor='transparent')
        root=result[0]
        #add Root
        directed_graph.node(root, fontsize='60', width='3', fixedsize='true', shape='circle', label='Beam '+str(root), style='filled', color=color+str(1))#label='beam '+str(root) #Brewer colors http://graphviz.org/doc/info/colors.html#brewer
        #add nodes and edges returned from assembly sequence
        for beams in result:
            weight=self.result_network.get_vertex_attribute(int(beams), 'weight')
            directed_graph.node(beams, fontsize='60', width='3', fixedsize='true', shape='circle', label='Beam '+str(beams), style='filled', color=color+str(weight))#, color='transparent')

#Network to generate assembly sequence
class Topology_Network(Network):
    def __init__(self, geometry_network, weights_list, beams_geometry):
        super(Topology_Network, self).__init__() 
        input_dict = {'edges': geometry_network.edges(data=True)}
        self.attributes.update(input_dict)
        self.beams_geometry=beams_geometry
        self.invert_network(weights_list)

    def invert_network (self, weights_list):
        #to translate from member being an edge to member being a vertex 
        #only the u value of each member is used and divided by 2.
        #thus it turns from being (u=0,u=2,u=4...) to (u=0,u=1,u=2...) 
        #iter member edges of geometry network
        for u,v,attr in self.attributes['edges']:
            if attr['edge_type']=='member':
                #get midpoint for each member edge of geometry network
                beam_edge_mid=midpoint_line((attr['u_coordinate'],attr['v_coordinate']))
                #create new vertex and use as coordinate the midpoint of u and v
                self.add_vertex(attr_dict={'x': beam_edge_mid[0], 'y' : beam_edge_mid[1], 'z' : beam_edge_mid[2]})#add beam_vertex
        #create adjacency dictionary
        adjacency_dict={}
        for u,v,attr in self.attributes['edges']:
            if attr['edge_type']=='member':
                temp_connected_vertex=[]
                #iter connected member edges of geometry network
                for connected_vertices in attr['member_edge_nbrs']:
                    #store connected member as its u value divided by 2 
                    temp_connected_vertex.append(connected_vertices[0]/2)
                adjacency_dict[u/2]=temp_connected_vertex
        #prepare adjacency dictionary for COMPAS traverse
        self.adjacency_dictionary=adjacency_dict
        #add adjacency and weight attribute to vertices
        for u, attr in self.vertices(data=True):
            self.set_vertex_attribute(u,'weight', weights_list[u])
            self.set_vertex_attribute(u,'connected_vertices', adjacency_dict[u])

if __name__ == "__main__":
    temp_frames_array = [] 
