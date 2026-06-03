from sage.all import *
from ..theta_structures.theta_helpers_dim4 import proj_batch_inversion_with_coeff

class Tree:
	def __init__(self,node):
		self._node=node
		self._edges=[]
		self._children=[]

	def add_child(self,child,edge):
		self._children.append(child)
		self._edges.append(edge)

	def look_node(self,node):
		if self._node==node:
			return self
		elif len(self._children)>0:
			for child in self._children:
				t_node=child.look_node(node)
				if t_node!=None:
					return t_node

	def edge_product(self,L_factors,factor_node=ZZ(1)):
		n=len(self._children)
		L_prod=[(factor_node,self._node)]
		for i in range(n):
			L_prod+=self._children[i].edge_product(L_factors,factor_node*L_factors[self._edges[i]])
		return L_prod


class Tree_new:
	def __init__(self,root,nodes_to_level,edge_to_ind,ind_to_edge,edge_num,edge_denom):
		self._root = root
		# nodes_to_level[i] = level of node i. -1 if not in support.
		self._nodes_to_level = nodes_to_level 
		# edge_to_ind[i+16*j] = -1 if i is not connected to j
		# edge_to_ind[i+16*j] = ind (between 0 and 15) if i -> j,
		# where ind indicates where values on the edges are stored 
		self._edge_to_ind = edge_to_ind
		self._ind_to_edge = ind_to_edge
		self._edge_num = edge_num
		self._edge_denom = edge_denom

	def edge_product(self,factor_num=1,factor_denom=1):
		# Constant time as long as n_edges is fix
		n_edges = len(self._edge_num)
		#height = max(self._nodes_to_level)
		edge_sequence = [0 for i in range(n_edges+1)]
		current = -1
		ind0 = self._root
		ind1 = 0
		for h in range(n_edges):
			for i in range(16):
				is_of_height_h = (self._nodes_to_level[i] == h)
				mask = (1<<(4*is_of_height_h))-1
				ind_start = ind0^((i^ind0)&mask)
				for j in range(16):
					connected_ind0_j = (self._edge_to_ind[ind_start+j*16] >= 0)
					mask = (1<<(4*(is_of_height_h&connected_ind0_j&(current<n_edges))))-1
					# if self._nodes_to_level[i] == h, then ind0 becomes i
					ind0 = ind0^((i^ind0)&mask)
					# if ind0 is connected to j, then ind1 becomes j
					ind1 = ind1^((j^ind1)&mask)

					# If a new edge has been discovered (i.e. i is of height h and i->j),
					# then current becomes current+1
					current = current+(is_of_height_h&connected_ind0_j&(current<n_edges))

					edge_sequence[current] = ind0+ind1*16

		edge_num = [factor_num]+self._edge_num
		edge_denom = [factor_denom]+self._edge_denom
		for i in range(n_edges):
			ind_edge = self._edge_to_ind[edge_sequence[i]]+1
			ind0 = edge_sequence[i]%16
			#ind1 = edge_sequence[i]//16

			ind_prev_edge = 0
			# Lookup for indm1, the parent of ind0 (root if ind0 is root)
			indm1 = self._root
			for i in range(16):
				connected_i_ind0 = (self._edge_to_ind[i+ind0*16] >= 0)
				mask = (1<<(4*connected_i_ind0))-1
				indm1 = indm1^((i^indm1)&mask)

			# If indm1 == ind0, then the previous edge is root-->root so ind_prev_edge is 0
			is_root = (indm1 == ind0)
			mask = (1<<(4*(1-is_root)))-1
			ind_prev_edge = ind_prev_edge^(((self._edge_to_ind[indm1+16*ind0]+1)^ind_prev_edge)&mask)

			edge_num[ind_edge]=edge_num[ind_prev_edge]*edge_num[ind_edge]
			edge_denom[ind_edge]=edge_denom[ind_prev_edge]*edge_denom[ind_edge]

		self._edge_num = edge_num[1:]
		self._edge_denom = edge_denom[1:]

	def invert_denom(self):
		edge_denom, lamb = proj_batch_inversion_with_coeff(self._edge_denom)
		self._edge_denom = edge_denom
		return lamb

def is_in(i,L):
	ret = False
	for ind in range(len(L)):
		ret = ret|(L[ind]==i)
	return ret 

def find_not_in(L,i_max=15):
	ret = 0
	for i in range(i_max+1):
		is_in_L = is_in(i,L)
		mask = (1<<(4*(1-is_in_L)))-1
		ret = ret^((i^ret)&mask)
	return ret

def field_select(x,y,sel):
	# TODO: implement in constant time in C
	if sel:
		return y
	else:
		return x

def fill_tree(HSK_8,L_ind_K_8=[1,2,4,8],L_ind_zeros=[]):
	n_zeros = len(L_ind_zeros)
	n_ker = len(L_ind_K_8)

	root = find_not_in(L_ind_zeros)
	nodes_to_level = [-1 for i in range(16)]
	edge_to_ind = [-1 for i in range(256)]
	edge_num = [0 for i in range(16-n_zeros)]
	edge_denom = [0 for i in range(16-n_zeros)]
	ind_to_edge = [0 for i in range(16-n_zeros)]
	
	nodes_to_level[root] = 0
	ind_current_edge = 0
	for step in range(n_ker):
		for i in range(16):
			is_in_tree_i = (nodes_to_level[i]>=0)
			for l in range(n_ker):
				j = i^L_ind_K_8[l]
				is_zero_j = is_in(j,L_ind_zeros)
				is_in_tree_j = (nodes_to_level[j]>=0)
				append_ij = is_in_tree_i&(1-is_zero_j)&(1-is_in_tree_j)&(ind_current_edge<15-n_zeros)&(HSK_8[l][i]!=0)&(HSK_8[l][j]!=0)

				# Update edges
				edge_num[ind_current_edge] = field_select(edge_num[ind_current_edge],HSK_8[l][i],append_ij)
				edge_denom[ind_current_edge] = field_select(edge_denom[ind_current_edge],HSK_8[l][j],append_ij)

				# Update height
				mask1 = (1<<(4*append_ij))-1
				i_or_j = i^((i^j)&mask1) # j if append_ij, i otherwise 
				nodes_to_level[i_or_j]= nodes_to_level[i]+append_ij

				# Reference edge index (1/2)
				mask2 = (1<<(8*append_ij))-1
				ind_to_edge[ind_current_edge] = ind_to_edge[ind_current_edge]^((ind_to_edge[ind_current_edge]^(i+16*j))&mask2)

				# Update index of current edge (for the next one to append)
				ind_current_edge = ind_current_edge+append_ij

				# Reference edge index (2/2)
				edge_to_ind[i+16*j] = edge_to_ind[i+16*j]+(ind_current_edge&mask1)

	return Tree_new(root,nodes_to_level,edge_to_ind,ind_to_edge[0:-1],edge_num[0:-1],edge_denom[0:-1])


				


















