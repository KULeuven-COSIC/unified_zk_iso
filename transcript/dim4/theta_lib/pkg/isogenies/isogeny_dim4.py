from sage.all import *

from ..theta_structures.Theta_dim4 import ThetaStructureDim4, ThetaPointDim4
from ..theta_structures.theta_helpers_dim4 import hadamard, squared, batch_inversion
from ..isogenies.tree import Tree, Tree_new, fill_tree

class IsogenyDim4:
	def __init__(self,domain,K_8,codomain=None,inv_null_point_dual=None):
		r"""
		Input:
		- domain: a ThetaStructureDim4.
		- K_8: a list of 4 points of 8-torision (such that 4*K_8 is a kernel basis), used to compute the codomain.
		- codomain: a ThetaStructureDim4 (for the codomain, used only when K_8 is None).
		- inv_null_point_dual: list of inverse of dual theta constants of the codomain, used to compute the image.
		"""

		if not isinstance(domain, ThetaStructureDim4):
			raise ValueError("Argument domain should be a ThetaStructureDim4 object.")
		self._domain = domain
		self._inv_null_point_dual=None
		if K_8!=None:
			self._compute_codomain_old(K_8)
		else:
			self._codomain=codomain
			self._inv_null_point_dual=inv_null_point_dual

	def _compute_codomain(self,K_8):
		r""" Too slow for now but works (good POC before the C implem).

		Input:
		- K_8: a list of 4 points of 8-torision (such that 4*K_8 is a kernel basis).

		Output:
		- codomain of the isogeny.
		Also initializes self._inv_null_point_dual, containing the inverse of theta-constants.
		"""


		HSK_8 = [hadamard(squared(P.coords())) for P in K_8]
		tree = fill_tree(HSK_8)

		tree.edge_product()

		lamb = tree.invert_denom()

		inv_null_point_dual = [None for i in range(16)]
		inv_null_point_dual[tree._root] = lamb
		for i in range(len(tree._ind_to_edge)):
			ind = tree._ind_to_edge[i]
			j = ind//16
			inv_null_point_dual[j] = tree._edge_num[i]*tree._edge_denom[i]

		# Duplicate memory for quick access but useless in C
		self._inv_null_point_dual = inv_null_point_dual

		self._codomain=ThetaStructureDim4(None,inv_null_point_dual=inv_null_point_dual)
        
        

	def _compute_codomain_old(self,K_8):
		r"""Will be deprecated in C (not constant time).

		Input:
		- K_8: a list of 4 points of 8-torision (such that 4*K_8 is a kernel basis).

		Output:
		- codomain of the isogeny.
		Also initializes self._inv_null_point_dual, containing the inverse of theta-constants.
		"""
        #2 lines of ZK stuff
		rad_x0 = sum([c**2 for c in self._domain.null_point().coords()])

		HSK_8=[hadamard(squared(P.coords())) for P in K_8]
		
		# Choice of reference index j_0<->chi_0 corresponding to a non-vanishing theta-constant.
		found_tree=False
		j_0=0
		while not found_tree:
			found_k0=False
			for k in range(4):
				if j_0>15:
					raise NotImplementedError("The codomain of this 2-isogeny could not be computed.\nWe may have encountered a product of abelian varieties\nsomewhere unexpected along the chain.\nThis is exceptionnal and should not happen in larger characteristic.")
				if HSK_8[k][j_0]!=0:
					k_0=k
					found_k0=True
					break
			if not found_k0:
				j_0+=1
			else:
				j0pk0=j_0^(2**k_0)
				# List of tuples of indices (index chi of the denominator: HS(f(P_k))_chi, 
				#index chi.chi_k of the numerator: HS(f(P_k))_chi.chi_k, index k).
				L_ratios_ind=[(j_0,j0pk0,k_0)]
				L_covered_ind=[j_0,j0pk0]

				# Tree containing the the theta-null points indices as nodes and the L_ratios_ind reference indices as edges.
				tree_ratios=Tree(j_0)
				tree_ratios.add_child(Tree(j0pk0),k_0)

				# Filling in the tree
				tree_filled=False
				while not tree_filled:
					found_j=False
					for j in L_covered_ind:
						for k in range(4):
							jpk=j^(2**k)
							if jpk not in L_covered_ind and HSK_8[k][j]!=0:
								L_covered_ind.append(jpk)
								L_ratios_ind.append((j,jpk,k))
								tree_j=tree_ratios.look_node(j)
								tree_j.add_child(Tree(jpk),len(L_ratios_ind)-1)
								found_j=True
								break
						if found_j:
							break
					if not found_j or len(L_covered_ind)==16:
						tree_filled=True
				if len(L_covered_ind)!=16:
					j_0+=1
				else:
					found_tree=True

		L_num=[HSK_8[t[2]][t[1]] for t in L_ratios_ind]
		L_denom=[HSK_8[t[2]][t[0]] for t in L_ratios_ind]
		L_num_inv=batch_inversion(L_num)
		L_ratios=[L_denom[i]*L_num_inv[i] for i in range(15)]

		L_coords_ind=tree_ratios.edge_product(L_ratios)

		O_coords=[ZZ(0) for i in range(16)]
		for t in L_coords_ind:
			O_coords[t[1]]=t[0]

		self._inv_null_point_dual=O_coords
		# Assumes there is no zero theta constant. Otherwise, squared(inv_null_point_dual) will raise an error (None**2 does not exist)
		self._codomain=ThetaStructureDim4(None,inv_null_point_dual=O_coords)
        #ZK: Scale projectively
		null_point_codomain = self._codomain.null_point()
		rad_y0 = sum([c for c in null_point_codomain.coords()])**2
		scaling_fac = ((rad_x0)/rad_y0).sqrt()
		scaled_null_point_codomain = [c*scaling_fac for c in null_point_codomain.coords()]
		self._codomain=ThetaStructureDim4(scaled_null_point_codomain)

	def codomain(self):
		return self._codomain

	def domain(self):
		return self._domain

	def image(self,P):
		HS_P=list(hadamard(squared(P.coords())))

		for i in range(16):
			HS_P[i] *=self._inv_null_point_dual[i]

		return self._codomain(hadamard(HS_P))

	def dual(self):
		return DualIsogenyDim4(self._codomain,self._domain, hadamard=True)

	def __call__(self,P):
		return self.image(P)


class DualIsogenyDim4:
	def __init__(self,domain,codomain,hadamard=True):
		# domain and codomain are respectively the domain and codomain of \tilde{f}: domain-->codomain,
		# so respectively  the codomain and domain of f: codomain-->domain.
		# By convention, domain input is given in usual coordinates (ker(\tilde{f})=K_2).
		# codomain is in usual coordinates if hadamard, in dual coordinates otherwise.
		self._domain=domain.hadamard()
		self._hadamard=hadamard
		if hadamard:
			self._codomain=codomain.hadamard()
			self._inv_null_point_dual=batch_inversion(codomain.zero().coords())
		else:
			self._codomain=codomain
			self._inv_null_point_dual=batch_inversion(codomain.zero().coords())

	def image(self,P):
		# When ker(f)=K_2, ker(\tilde{f})=K_1 so ker(\tilde{f})=K_2 after hadamard transformation of the 
		# new domain (ex codomain)
		HS_P=list(hadamard(squared(P.coords())))
		for i in range(16):
			HS_P[i] *=self._inv_null_point_dual[i]
		if self._hadamard:
			return self._codomain(hadamard(HS_P))
		else:
			return self._codomain(HS_P)

	def __call__(self,P):
		return self.image(P)
