from compas.datastructures.network import Network
from compas_fab.fab.geometry import Frame, Transformation
from compas.geometry.elements import Line
from compas.geometry import distance_point_point
from collections import deque
import random as r
from graphviz import Digraph
from heap import Heap
import random
import operator
r.seed(1)

__author__     = 'Augusto Gandia'
__copyright__  = 'Copyright 2018, Gramazio Kohler Research - ETH Zurich'
__license__    = 'MIT'
__email__      = 'gandia@arch.ethz.ch'

def setup(rawData):
        cities = list()
        #Create and return sorted data in list
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

# Method to perform Kruskal's Algorithm    
def kruskal(data,cities):
    distance = 0
    result = list()
    cities = init(cities)
    for edge in range(len(data)):
        path = data.pop(0)
        #If the two cities in the path do not have the same
        #canonical representative, join them together, then 
        #add path to result and calculate distance
        if find(cities,path[0]) != find(cities,path[1]):
            union(cities, path[0],path[1])
            result.append(path[0])
            result.append(path[1])
            result.append(path[2])
            distance += path[2]
    return result,distance

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

class ToleranceNetwork(Network):
    """multiple networks for tolerance analysis of spatial structures """
    def __init__(self, edges_joint, edges_beam, ordered_beams, weights_list):

        super(ToleranceNetwork, self).__init__() 
        input_dict = {'edges_joint': edges_joint, 'edges_beam': edges_beam, 'ordered_beams': ordered_beams}
        self.attributes.update(input_dict)
        self.generate_vertices()
        self.generate_joint_edges()
        self.store_connectivity_in_member_edges()
        self.generate_topology_network(weights_list)
        self.MST_Kruskal()
        #self.draw_MST_Kruskal() 

    def MST_Kruskal(self):
        #Adjacency dictionary for COMPAS deph_first_tree
        adjacency_dictionary=self.topology_network.adjacency_dictionary
        #Sort 
        r = []
        #Iterate nodes
        for n in adjacency_dictionary:
            parent_weight = self.topology_network.get_vertex_attribute(n, 'weight')
            #Iterate neighbours of each node
            for nbr in adjacency_dictionary[n]:

                child_weight = self.topology_network.get_vertex_attribute(nbr, 'weight') 
                parent = [str(nbr), str(n), parent_weight]
                child = [str(n), str(nbr), child_weight]
                if parent_weight > child_weight:
                    r.append(parent)
                    if child in r:
                        r.remove(child)
                else:
                    r.append(child)
                    if parent in r:
                        r.remove(parent)
        r = sorted(r, key=operator.itemgetter(2))
        data = r
        cities = map(str, self.topology_network.vertices())
        result,distance = kruskal(data,cities)
        self.result=result
        # print self.result, distance
        #Remove duplicates
        assembly_sequence=[]
        #for step in self.result[1:][::3]:
        for step in self.result:
            #skip weights and remove multiple connections to add beam
            if isinstance(step, str) and step not in assembly_sequence:
                assembly_sequence.append(step)
        self.assembly_sequence = assembly_sequence

    def draw_MST_Kruskal(self):

        #adjacency_dictionary
        adjacency_dictionary=self.topology_network.adjacency_dictionary
        #color convention
        color="/rdbu8/"
        #setup
        directed_graph=Digraph(format='png')
        directed_graph.attr(ranksep='7', resolution='80', lheight='1000', lwidth='2000', smoothing='true')#, bgcolor='transparent')
        root=self.assembly_sequence[0]
        #add Root
        directed_graph.node(root, fontsize='60', width='3', fixedsize='true', shape='circle', label='Beam '+str(root), style='filled', color=color+str(1))#label='beam '+str(root) #Brewer colors http://graphviz.org/doc/info/colors.html#brewer
        #add nodes and edges returned from assembly sequence

        for n in self.assembly_sequence:
            weight=self.topology_network.get_vertex_attribute(int(n), 'weight')
            directed_graph.node(n, fontsize='60', width='3', fixedsize='true', shape='circle', label='Beam '+str(n), style='filled', color=color+str(weight))#, color='transparent')

        weighted_edges=[self.result[int(i):int(i) + 3] for i in range(0, len(self.result), 3)]
        for e in weighted_edges:
            directed_graph.edge(e[0],e[1], headlabel=str(e[2]), labeldistance='6', fontsize='60', arrowsize='3')#, fontcolor=color+str(int(weight)))

        directed_graph.render(filename = 'C:/Users/gandiaa/Documents/projects/tolerance_analysis/connectivity_graph', cleanup=True)

        """
        #adjacency_dictionary
        adjacency_dictionary=self.topology_network.adjacency_dictionary
        #set root
        root=str(self.paths[0][0])
        #setup
        directed_graph=Digraph(format='png')#format='png')
        directed_graph.attr(ranksep='7', resolution='80', lheight='1000', lwidth='2000', smoothing='true', bgcolor='transparent')
        #color convention
        color="/rdbu8/"
        #add Root
        #directed_graph.node(root, fontsize='60', width='3', fixedsize='true', shape='circle', label='Beam '+str(root), style='filled', color=color+str(1))#label='beam '+str(root) #Brewer colors http://graphviz.org/doc/info/colors.html#brewer
        #add nodes and edges returned from breadth_first tree
        added_edges=[]
        for tree in self.paths:
            level=int(len(tree)-1)
            node=str(tree[level])
            color_by_weight=self.topology_network.get_vertex_attribute(int(node), 'weight')
            directed_graph.node(node, fontsize='60', width='3', fixedsize='true', shape='circle', label='Beam '+str(node), style='filled', color='transparent')# color=color+str(color_by_weight))#width='0.5', fixedsize='true', label='beam '+str(node)#Brewer colors http://graphviz.org/doc/info/colors.html#brewer
            if len(tree) != 1:
                parent=str(tree[len(tree)-2])
                child=str(tree[len(tree)-1])
                i=self.paths.index(tree)-1
                weight=self.breadth_first_weighted_edges[i].split(' ')[2]
                directed_graph.edge(parent,child, headlabel=str(weight), labeldistance='6', fontsize='60', arrowsize='3')#, fontcolor=color+str(int(weight)))
                added_edges.append((parent,child))
        
        #add not selected edges
        for ordered_node in self.ordering:
            for connected_node in adjacency_dictionary[ordered_node]:
                ordered_node=str(ordered_node)
                connected_node=str(connected_node) 
                if (ordered_node,connected_node) not in added_edges and (connected_node,ordered_node) not in added_edges:
                    weight=self.topology_network.get_vertex_attribute(int(connected_node), 'weight')
                    directed_graph.edge(ordered_node,connected_node,constraint='false', color='grey80')
                    added_edges.append((ordered_node,connected_node))

        counter=0
        for key in self.assembly_sequence:
            #for node in list(directed_graph)[3:]:
            for node in directed_graph.body:
                key = str(key)
                if node.startswith('\t%s [' % key):
                    weight=self.topology_network.get_vertex_attribute(int(key), 'weight')
                    index=directed_graph.body.index(node)
                    directed_graph.body[index]=directed_graph.body[index].replace('style=filled', 'style=filled,color="/rdbu8/'+str(weight)+'"')
                    #directed_graph.render(filename = 'C:/Users/gandiaa/Documents/projects/tolerance_analysis/connectivity_graph_'+str(counter), cleanup=True)     
                    counter+=1
        #render
        #directed_graph.render(filename = 'C:/Users/gandiaa/Documents/projects/tolerance_analysis/connectivity_graph', cleanup=True)
        """   
    
    def generate_vertices(self):
        #add in network, vertices of edge beams
        for index in range(len(self.attributes ['edges_beam'])):
            #add edge vertex u
            position = self.attributes ['edges_beam'][index][0]
            u=self.add_vertex(attr_dict={'x': position[0], 'y' : position[1], 'z' : position[2], 'vertex_type': 'member'})
            #add edge vertex v
            position = self.attributes ['edges_beam'][index][1]
            v=self.add_vertex(attr_dict={'x': position[0], 'y' : position[1], 'z' : position[2], 'vertex_type': 'member'})
            #add attribute edge type and asociate beam
            neighbours_member_edges=[]
            self.add_edge(u,v, {'edge_type': 'member','beam': self.attributes ['ordered_beams'][index], 'u_coordinate':self.vertex_coordinates(u), 'v_coordinate': self.vertex_coordinates(v), 'neighbours_member_edges': neighbours_member_edges})

    def generate_joint_edges(self):
        store_beam_u=[]
        store_beam_v=[]
        for edge_joint in range (len(self.attributes['edges_joint'])):
            joint_u=self.attributes ['edges_joint'][edge_joint][0]
            joint_v=self.attributes ['edges_joint'][edge_joint][1]
            for u,v,attr in self.edges(data=True):
                beam_u=attr['u_coordinate']
                beam_v=attr['v_coordinate']
                if distance_point_point(joint_u,beam_u) < 50:
                    joint_new_vertex_u=[]
                    joint_new_vertex_u.append(u)
                if distance_point_point(joint_u,beam_v) < 50:
                    joint_new_vertex_u=[]
                    joint_new_vertex_u.append(v)
                if distance_point_point(joint_v,beam_u) < 50:
                    joint_new_vertex_v=[]
                    joint_new_vertex_v.append(u)
                if distance_point_point(joint_v,beam_v) < 50:
                    joint_new_vertex_v=[]
                    joint_new_vertex_v.append(v)
            store_beam_u.append(joint_new_vertex_u[0])
            store_beam_v.append(joint_new_vertex_v[0])
        for iterate in range(len(store_beam_v)):
            self.add_edge(store_beam_u[iterate], store_beam_v[iterate], {'edge_type': 'joint','beam': None})

    def store_connectivity_in_member_edges(self):
        #store connectivity in joint edges
        for u,v,attr in self.edges(data=True):#181
            if attr['edge_type']=='joint':
                connected_joint_edges_list=edge_connected_edges(self,u,v) #per beam edge a list of connected joint edges
                prev_list=[]
                #filter connected joint edges and store connected member edges
                for joint_edge in connected_joint_edges_list:
                    if self.get_edge_attribute(joint_edge[0],joint_edge[1],'edge_type')=='member':   
                        prev_list.append((joint_edge[0],joint_edge[1])) 
                #get existing neighbours from first edge
                first_edge_neighbours=self.get_edge_attribute(prev_list[0][0],prev_list[0][1],'neighbours_member_edges')
                first_edge_neighbours.append(prev_list[1])
                #get existing neighbours from second edge
                sec_edge_neighbours=self.get_edge_attribute(prev_list[1][0],prev_list[1][1],'neighbours_member_edges')
                sec_edge_neighbours.append(prev_list[0])
    
    def generate_topology_network(self, weights_list):
        #this "topology network" is an inversion of the "geometry_network" by turning beams into vertices
        self.topology_network=TopologyNetwork(self, weights_list)

class TopologyNetwork(Network):
    def __init__(self, geometry_network, weights_list):
        super(TopologyNetwork, self).__init__() 
        input_dict = {'edges': geometry_network.edges(data=True)}
        self.attributes.update(input_dict)
        self.invert_network(weights_list)

    def invert_network(self, weights_list):
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
                for connected_vertices in attr['neighbours_member_edges']:
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
