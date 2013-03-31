/*
 * ArchE
 * Copyright (c) 2012 Carnegie Mellon University.
 * All Rights Reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions are met:
 *
 * 1. Redistributions of source code must retain the above copyright notice,
 * this list of conditions and the following acknowledgments and disclaimers.
 *
 * 2. Redistributions in binary form must reproduce the above copyright notice,
 * this list of conditions and the following disclaimer in the documentation
 * and/or other materials provided with the distribution.
 *
 * 3. All advertising materials for third-party software mentioning features or
 * use of this software must display the following disclaimer:
 *
 * “Neither Carnegie Mellon University nor its Software Engineering Institute
 * have reviewed or endorsed this software”
 *
 * 4. The names “Carnegie Mellon University,” and/or “Software Engineering
 * Institute" shall not be used to endorse or promote products derived from
 * this software without prior written permission. For written permission,
 * please contact permission@sei.cmu.edu.
 *
 * 5. Redistributions of any form whatsoever must retain the following
 * acknowledgment:
 *
 * Copyright 2012 Carnegie Mellon University.
 *
 * This material is based upon work funded and supported by the United States
 * Department of Defense under Contract No. FA8721-05-C-0003 with Carnegie
 * Mellon University for the operation of the Software Engineering Institute, a
 * federally funded research and development center.
 *
 * NO WARRANTY
 *
 * THIS CARNEGIE MELLON UNIVERSITY AND SOFTWARE ENGINEERING INSTITUTE MATERIAL
 * IS FURNISHED ON AN “AS-IS” BASIS. CARNEGIE MELLON UNIVERSITY MAKES NO
 * WARRANTIES OF ANY KIND, EITHER EXPRESSED OR IMPLIED, AS TO ANY MATTER
 * INCLUDING, BUT NOT LIMITED TO, WARRANTY OF FITNESS FOR PURPOSE OR
 * MERCHANTABILITY, EXCLUSIVITY, OR RESULTS OBTAINED FROM USE OF THE MATERIAL.
 * CARNEGIE MELLON UNIVERSITY DOES NOT MAKE ANY WARRANTY OF ANY KIND WITH
 * RESPECT TO FREEDOM FROM PATENT, TRADEMARK, OR COPYRIGHT INFRINGEMENT.
 */

package arche.modifChangeImpact;

/**
 * An implementation of a module view (used by modifiability reasoning framework)
 * 
 * @author Hyunwoo Kim, Andres Diaz-Pace
 */

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import org.hibernate.HibernateException;
import org.hibernate.Query;
import org.hibernate.Session;

import arche.modifChangeImpact.hibernate.ArchECoreDataProvider;
import arche.modifChangeImpact.hibernate.ArchECoreResponsibilityStructure;
import arche.modifChangeImpact.hibernate.ArchECoreView;
import arche.modifChangeImpact.hibernate.vo.ArchEModuleDependencyRelationVO;
import arche.modifChangeImpact.hibernate.vo.ArchEModuleVO;
import arche.modifChangeImpact.hibernate.vo.ArchEResponsibilityToModuleRelationVO;
import arche.modifChangeImpact.hibernate.vo.ArchEResponsibilityVO;
import arche.modifChangeImpact.hibernate.vo.ArchEVersionVO;

import edu.cmu.sei.arche.ArchEException;
import edu.cmu.sei.arche.external.data.ArchEArchitecture;
import edu.cmu.sei.arche.external.data.ArchEResponsibility;

public class ModuleADLWrapper extends ArchECoreView implements RFModuleView {

	private static final int MAX_ALLOCATION_PER_MODULE 	= 50;
	private static final int MAX_MODULES 				= 50;

	private boolean [][] dependencyMatrix; // Dependencies among modules (according to the responsibilities allocated to them)
	private boolean [][] allocationMatrix; // Mapping from responsibilities to modules
	private ArchEModuleVO[] modules = null; // The current modules in the view
	private ArchEResponsibility[] allocatedResponsibilities = null; // The current responsibilities allocated to the modules
	private int countModules = -1;
	private int countResponsibilities = -1;
		
	// Lists of raw VOs used when restoring/saving/updating/deleting VOs from the DB
	private List<ArchEModuleVO> rawModuleVOs = null;
	private List<ArchEModuleDependencyRelationVO> rawModuleDependencies = null;
	private List<ArchEResponsibilityToModuleRelationVO> rawResponsibilityAllocations = null;
	
	public ModuleADLWrapper(ArchEArchitecture architecture) {
		super(architecture);
		
		dependencyMatrix = new boolean[MAX_MODULES][MAX_MODULES];
		allocationMatrix = new boolean[MAX_MODULES][MAX_ALLOCATION_PER_MODULE];
		modules = new ArchEModuleVO[MAX_MODULES];
		allocatedResponsibilities = new ArchEResponsibility[MAX_ALLOCATION_PER_MODULE];
		countModules = 0;
		countResponsibilities = 0;		
	}
	
	protected void reset() {
		countModules = 0;
		countResponsibilities = 0;	
	}
	
	/** 
	 * It returns the index of an existing responsibility (already allocated to some module)
	 */
	protected int getResponsibilityIndex(ArchEResponsibility responsibility) {
		
		for (int i = 0; i < countResponsibilities; i++) {
			// The two responsibilities are equal if  they have the same name
			// (under the same version of the architecture)
			if (allocatedResponsibilities[i].getName().equals(responsibility.getName()))
				return (i);
		}
		
		return (-1);
	}

	/** 
	 * It returns the index of an existing module or -1 otherwise
	 */
	protected int getModuleIndex(ArchEModuleVO module) {
		
		for (int i = 0; i < countModules; i++) {
			// The two modules are equal if  they have the same name
			// (under the same version of the architecture)
			if (modules[i].getName().equals(module.getName()))
				return (i);
		}
		
		return (-1);
	}
	
	/** 
	 * It checks if a dependency exists between two existing modules
	 */
	public boolean hasDependency(ArchEModuleVO mod1, ArchEModuleVO mod2) {
		
		int i = this.getModuleIndex(mod1);
		if (i == -1) // The module doesn't exist
			return (false);
		
		int j = this.getModuleIndex(mod2);  
		if (j == -1) // The module doesn't exist
			return (false);
		
		return (dependencyMatrix[i][j]);
	}
	
	/** 
	 * It checks if a responsibility is allocated to a given module
	 */
	public boolean isAllocated(ArchEResponsibility resp, ArchEModuleVO module) {
		
		int i = this.getModuleIndex(module);
		if (i == -1) // The module doesn't exist
			return (false);
		
		int j = this.getResponsibilityIndex(resp);
		if (j == -1) // The responsibility doesn't exist
			return (false);
		
		return (allocationMatrix[i][j]);
	}

	/** 
	 * It checks if a responsibility is allocated to some existing module
	 */
	public boolean isAllocated(ArchEResponsibility resp) {
		
		int j = this.getResponsibilityIndex(resp);
		if (j == -1) // The responsibility doesn't exist
			return (false);
		
		for (int i = 0; i < countModules; i++) {
			if (allocationMatrix[i][j])
				return (true);			
		}
		
		return (false);
	}
	
	// It returns the number of responsibilities effectively allocated to modules
	// (this method is only for checking consistency in the allocation of 
	// responsibilities when compared to the current responsibility structure)
	public int getCountAllocatedResponsibilities() {
		return (countResponsibilities);
	}

	public int getCountAllocatedResponsibilities(ArchEModuleVO module) {
		int countAllocations = 0;
		int i = this.getModuleIndex(module);
		if (i != -1) { // The module exists
			for (int j = 0; j < countResponsibilities; j++) {
				if (allocationMatrix[i][j])
					countAllocations++;
			}
		}
		return (countAllocations);
	}
	
	public int getCountModuleDependencies() {
		int countDependencies = 0;
		for (int i = 0; i < countModules; i++) {
			for (int j = 0; j < i; j++) { // It only counts under the matrix diagonal
				if (dependencyMatrix[i][j])
					countDependencies++;
			}
		}
		return (countDependencies);
	}

	/** 
	 * It checks if two existing responsibilities are allocated to the same module
	 */
	public boolean areCoAllocated(ArchEModuleVO module, ArchEResponsibility resp1, ArchEResponsibility resp2) {
		
		int i = this.getModuleIndex(module);
		if (i == -1)  // The module doesn't exist
			return (false);
		
		int j = this.getResponsibilityIndex(resp1);
		if (j == -1)  // The responsibility doesn't exist
			return (false);
		
		int k = this.getResponsibilityIndex(resp2);
		if (k == -1)  // The responsibility doesn't exist
			return (false);
		
		return (allocationMatrix[i][j] && allocationMatrix[i][k]);
	}
	
	/** 
	 * It checks if two existing responsibilities are allocated to some shared module
	 */
	public boolean areCoAllocated(ArchEResponsibility resp1, ArchEResponsibility resp2) {
		
		int j = this.getResponsibilityIndex(resp1);
		if (j == -1)  // The responsibility doesn't exist
			return (false);
		
		int k = this.getResponsibilityIndex(resp2);
		if (k == -1)  // The responsibility doesn't exist
			return (false);
		
		for (int i = 0; i < countModules; i++) {			
			if (areCoAllocated(modules[i],resp1,resp2))
				return (true);
		}
		
		return (false);
	}

	/** 
	 * It establishes (or deletes) a dependency between two existing modules
	 */
	public boolean setModuleDependency(ArchEModuleVO mod1, ArchEModuleVO mod2, boolean value) {
		
		int pos1 = this.getModuleIndex(mod1);
		if (pos1 == -1)  // The module doesn't exist
			return (false);
		
		int pos2 = this.getModuleIndex(mod2);
		if (pos2 == -1) // The module doesn't exist
			return (false);
		
		dependencyMatrix[pos1][pos2] = value; // Dependency is bidirectional
		dependencyMatrix[pos2][pos1] = value; // Dependency is bidirectional
		
		return (true);
		
		// Note: Since the relations module-module or module-responsibility may change (true or false)
		// during the lifetime of the view, there is a 'lazy' update of corresponding raw relationVOs.
		// This update is only performed when the view is restored (and the reasoning framework
		// calls loadsWithConsistencyChecking()) and when the view is saved (via methods
		// updateResponsibilityAllocationVOs() and updateModuleDependencyVOs())
		// Therefore, here there's NO UPDATE of rawModuleDependencyVOs

	}	

	/** 
	 * It establishes (or deletes) an allocation relationship between
	 * a module and a relationship
	 */ 
	public boolean setResponsibilityAllocation(ArchEModuleVO module, 
							ArchEResponsibility resp, boolean value) {
		
		int pos1 = this.getModuleIndex(module);
		if (pos1 == -1)  // The module doesn't exist
			return (false);
		
		int pos2 = this.getResponsibilityIndex(resp);
		if (pos2 == -1)  // The responsibility doesn't exist
			return (false);
		
		allocationMatrix[pos1][pos2] = value; 
		
		// TODO: If the responsibility is not allocated to any other module within the view, 
		// maybe the responsibility should be also removed from vector 'allocatedResponsibilities'
		
		// TODO: When changes happen in the allocation of responsibilities, should the 
		// dependencies between components be updated?
		
		// NOTE: Since the relations module-module or module-responsibility may change (true or false)
		// during the lifetime of the view, there is a 'lazy' update of corresponding relationVOs.
		// This update is only performed when the view is restored (and the reasoning framework
		// calls loadsWithConsistencyChecking()) and when the view is saved (via methods
		// updateResponsibilityAllocationVOs() and updateModuleDependencyVOs())
		
		// Therefore, here there's NO UPDATE of rawResponsibilityAllocationVOs
		
		return (true);
	}	
	
	/** 
	 * It registers a new responsibility for allocation to some module
	 * (precondition to invoke method 'setResponsibiltyAllocation' successfully)
	 */
	public boolean defineResponsibility(ArchEResponsibility responsibility) {		
		
		int index = this.getResponsibilityIndex(responsibility);
		if (index == -1) { // The responsibility is a new one
			
			if (countResponsibilities == MAX_ALLOCATION_PER_MODULE - 1)
				return (false); // The allocation matrix doen't support new responsibilities

			// If not, the new responsibility is registered
			allocatedResponsibilities[countResponsibilities] = responsibility;
			countResponsibilities++; 
			
			for (int i = 0; i < countModules; i++)
				allocationMatrix[i][countResponsibilities] = false;

			return (true);

		}

		return (false);
	}

	/** 
	 * It registers a new module within the view
	 * (precondition to invoke methods 'setModuleDependency' and 'setResponsibiltyAllocation')
	 */
	public boolean defineModule(ArchEModuleVO module) {
		
		int index = this.getModuleIndex(module);
		if (index == -1) { // The module is a new one

			if (countModules == MAX_MODULES - 1)
				return (false); // The module vector is full

			// If not, the new module is added
			modules[countModules] = module;
			countModules++; 
			
			// The dependencies are updated
			for (int i = 0; i < countModules; i++)
				dependencyMatrix[i][countModules] = false;
			dependencyMatrix[countModules][countModules] = true;
			
			// The allocations are updated
			for (int i = 0; i < countResponsibilities; i++)
				allocationMatrix[countModules][i] = false;
			
			return (true);
			
		}
		
		return (false);
	}

	/** 
	 * It returns all the modules defined for this view that contain a 
	 * specific responsibility
	 */
	public List<ArchEModuleVO> getModulesByResponsibility(ArchEResponsibility responsibility) {

		ArrayList<ArchEModuleVO> list = new ArrayList<ArchEModuleVO>();
		
		int pos = this.getResponsibilityIndex(responsibility);
		if (pos == -1) // The responsibility doesn't exist within the view
			return list;
		
		for (int i = 0; i < countModules; i++) {
			if (allocationMatrix[i][pos]) {
				list.add(modules[i]);
			}
		}
		
		return (list);
	}

	public List<ArchEModuleVO> getModules() {
		
		ArrayList<ArchEModuleVO> list = new ArrayList<ArchEModuleVO>();
	
		for (int i = 0; i < countModules; i++) {
			list.add(modules[i]);			
		}
		
		return (list);
	}

//	// It returns all the VO modules defined for this view and updates the rawModuleVOs list
//	// (this method should be used when executing save/delete operations on the database)
//	protected List<ArchEModuleVO> updateModules() {
//		
//		for (int i = 0; i < countModules; i++) {
//			// It updates the list of VOs with those that may be defined using 'defineModule()',
//			// but not necessarily stored in the rawModuleVOs list
//			if (!rawModuleVOs.contains(modules[i]))
//				rawModuleVOs.add(modules[i]);
//		}	
//	
//		// Note that 'deleted' modules have been already removed from rawModuleVOs through
//		// 'removeModule()', which in turns calls 'deleteDesignElement'
//		
//		return (rawModuleVOs);
//	}

	/** 
	 * It returns all the responsibilities allocated to a particular module in this view
	 */
	public List<ArchEResponsibility> getResponsibilitiesByModule(ArchEModuleVO module) {

		ArrayList<ArchEResponsibility> list = new ArrayList<ArchEResponsibility>();

		int pos = this.getModuleIndex(module);		
		if (pos != -1) { // The module exists in the view			
			ArchEResponsibility resp = null;
			for (int j = 0; j < countResponsibilities; j++) { 
				if (allocationMatrix[pos][j])  // There is an allocation relationship
					list.add(allocatedResponsibilities[j]);
			}					
		}

		return (list);
	}
	
	/**
	 * It deletes a module from the current view, and it also keeps the module
	 * as a VO to be removed when invoking the save() operation in the DB 
	 */
	public boolean removeModule(ArchEModuleVO module) {
		
		this.deleteDesignElement(module);		
		
		int pos = this.getModuleIndex(module);
		
		if (pos != -1) { // The module exists  within the view			
		
			for (int i = pos ; i < countModules -1; i++) 
				modules[i] = modules[i+1];
			
			// Updating the dependencies between modules
			for (int j = pos; j < countModules; j++) // Moving the rows up				
				for (int k = 0; k < countModules; k++)
					dependencyMatrix[j][k] = dependencyMatrix[j+1][k];
			for (int j = pos; j < countModules-1; j++) // Moving the columns back				
				for (int k = pos; k < countModules-1; k++)
					dependencyMatrix[j][k] = dependencyMatrix[j][k+1];

			// Updating the allocation of responsibilities
			for (int m = pos; m < countModules -1; m++) // Moving the rows up
				for (int n = 0; n < countResponsibilities; n++)
					allocationMatrix[m][n] = allocationMatrix[m+1][n];
			
			countModules--;
			
			return (true);
		
		}
		return (false);
	}

	/**
	 * It deletes a responsibility from the current view
	 */
	public boolean removeResponsibility(ArchEResponsibility responsibility) {
		
		int pos = this.getResponsibilityIndex(responsibility);
		
		if (pos != -1) { // The responsibility exists within the view
			
			for (int i = pos; i < countResponsibilities -1; i++) 
				allocatedResponsibilities[i] = allocatedResponsibilities[i+1];
			
			// Updating the allocation of responsibilities
			for (int m = 0; m < countModules; m++) // Moving the columns back
				for (int n = pos; n < countResponsibilities-1; n++)
					allocationMatrix[m][n] = allocationMatrix[m][n+1];

			countResponsibilities--;
			
			return (true);
		}
		return (false);
	}

	// It returns all the actual VO allocation relations defined for this view, and updates the 
	// rawResponsibilityAllocations list (this method should be used when executing 
	// save/delete operations on the database)
	protected List<ArchEResponsibilityToModuleRelationVO> updateResponsibilityAllocationVOs() {
		
		ArchEResponsibilityToModuleRelationVO rel = null;
		ArchEVersionVO versionVO = (ArchEVersionVO)this.getParent().getCurrentVersion();
		
		// It looks for dangling allocations (because their parents modules were deleted by some tactic)
		boolean danglingAllocation = false;
		for (Iterator<ArchEResponsibilityToModuleRelationVO> itAllocations = rawResponsibilityAllocations.iterator(); 
			itAllocations.hasNext();) {
			rel = itAllocations.next();
			danglingAllocation = true;
			for (int i = 0; i < countModules; i++) {
				for (int j = 0; j < countResponsibilities; j++) {
					if (rel.getParent().equals(modules[i])
							&& rel.getChild().equals(allocatedResponsibilities[j])) 
						danglingAllocation = false; // There's still some parent/child for the allocation					
				}
			}
			if (danglingAllocation) {
				itAllocations.remove();
				this.deleteDesignRelation(rel);							
			}
		}
		
		// It traverses all the current allocations of responsibilities to modules
		// Note that only allocations for 'actual' modules are synchronized (this assumes
		// that allocations for removed modules have been deleted somehow before)
		for (int i = 0; i < countModules; i++) {
			for (int j = 0; j < countResponsibilities; j++) {
				
				rel = this.findAllocationRelationVO(modules[i], allocatedResponsibilities[j]);
				
				if (allocationMatrix[i][j]) { 					
					// In case there exist a relation between a module and a responsibility 
					// (as given by the current allocation matrix)
					if (rel == null) {
						// The relation didn't exist when rawResponsibilityAllocations was loaded,
						rel = new ArchEResponsibilityToModuleRelationVO(versionVO);
						rel.setParent(modules[i]); // A new relation is created and stored
						rel.setChild((ArchEResponsibilityVO)allocatedResponsibilities[j]);
						rawResponsibilityAllocations.add(rel);
					}
					// else: The relation comes from when rawResponsibilityAllocations was loaded
					// If so, nothing needs to be updated in the VO list for allocations
				
				} 
				else {
					// In case there's no relation between a module and a responsibility
					// (as given by the current allocation matrix)
					if (rel != null) {
						// There is an old relation still in rawResponsibilityAllocations (that
						// was set when rawResponsibilityAllocations was loaded, and then removed
						// by some operation on the view)
						rawResponsibilityAllocations.remove(rel);
						this.deleteDesignRelation(rel);
					}				
					// else: the relation is not neither in rawResponsibilityAllocations
					// nor in the matrix. If so, nothing needs to be updated
					
				} // End main if-else for allocationMatrix[i][j]
			}
		}
		
		return (rawResponsibilityAllocations);
	}
	
	private ArchEResponsibilityToModuleRelationVO findAllocationRelationVO(ArchEModuleVO module, ArchEResponsibility resp) {
		ArchEResponsibilityToModuleRelationVO allocation = null;
		for(Iterator<ArchEResponsibilityToModuleRelationVO> it = rawResponsibilityAllocations.iterator(); it.hasNext();) {
			allocation = it.next();
			if (allocation.getParent().equals(module) && allocation.getChild().equals(resp))
				return (allocation);
		}
		return (null);
	}

	// It returns all the actual VO module dependency relations defined for this view, and updates the 
	// rawModuleDependencies list (this method should be used when executing save/delete 
	// operations on the database)
	protected List<ArchEModuleDependencyRelationVO> updateModuleDependencyVOs() {		
		
		ArchEModuleDependencyRelationVO rel = null;
		ArchEVersionVO versionVO = (ArchEVersionVO)this.getParent().getCurrentVersion();
		
		// It traverses all the current dependencies between modules
		for (int i = 0; i < countModules; i++) {
			//for (int j = 0; j < countModules; j++) {
			for (int j = 0; j < i; j++) { // It just checks the triangle under the matrix
				// diagonal, because the dependencies between modules are supposed to be symmetrical				
				rel = this.findModuleDependencyVO(modules[i], modules[j]);
				
				if (dependencyMatrix[i][j]) { 					
					// In case there exist a relation between two modules
					// (as given by the current dependency matrix)
					if (rel == null) {
						// The relation was set AFTER the rawModuleDependencies was loaded
						rel = new ArchEModuleDependencyRelationVO(versionVO);
						rel.setParent(modules[i]); // A new relation is created and stored
						rel.setChild(modules[j]);
						rawModuleDependencies.add(rel);
					}
					// else: The relation comes from when rawModuleDependencies was loaded
					// If so, nothing needs to be updated
				
				} 
				else {
					// In case there's no relation between this pair of modules
					// (as given by the current dependency matrix)
					if (rel != null) {
						// There is an old relation still in rawModuleDependencies (that
						// was set when rawModuleDependencies was loaded, and then removed
						// by some operation on the view)
						rawModuleDependencies.remove(rel);
						this.deleteDesignRelation(rel);
					}				
					// else: the relation is not neither in rawModuleDependencies
					// nor in the matrix. If so, nothing needs to be updated
					
				} // End main if-else for dependencyMatrix[i][j]
			}
		}
		
		return (rawModuleDependencies);
	}
	
	private ArchEModuleDependencyRelationVO findModuleDependencyVO(ArchEModuleVO mod1, ArchEModuleVO mod2) {
		ArchEModuleDependencyRelationVO modDependency = null;
		for(Iterator<ArchEModuleDependencyRelationVO> it = rawModuleDependencies.iterator(); it.hasNext();) {
			modDependency = it.next();
			if (modDependency.getParent().equals(mod1) && modDependency.getChild().equals(mod2))
				return (modDependency);
			if (modDependency.getParent().equals(mod2) && modDependency.getChild().equals(mod1))
				return (modDependency);
		}
		return (null);
	}	

	/**
	 * It ensures that the module view is loaded consistently from the database. 
	 * The consistency rules refer to: allocation of 'current' responsibilities only, 
	 * deletion of 'dangling' dependencies between modules, and also elimination of 
	 * modules with no responsibilities allocated to them.
	 * 
	 * @param responsibilities The current responsibility structure the module should be consistent with
	 */
	public boolean loadViewWithConsistencyChecking(ArchECoreResponsibilityStructure responsibilities){
		
		this.reset();
		
		// Step 1: Recover the 'old' list of modules
    	for (Iterator<ArchEModuleVO> it = rawModuleVOs.iterator(); it.hasNext();) 
    		this.defineModule(it.next());

    	// Step 2: Only set those allocation relation with 'valid' responsibilities
    	ArchEResponsibilityToModuleRelationVO tempAllocation = null;
    	boolean allocated = false;
    	ArchEResponsibilityVO resVO = null;
    	ArchEModuleVO modVO = null;
    	for (Iterator<ArchEResponsibilityToModuleRelationVO> it = rawResponsibilityAllocations.iterator(); it.hasNext();) {
    		tempAllocation = it.next();
    		resVO = tempAllocation.getChild();
    		modVO = tempAllocation.getParent();
    		if ((resVO == null) || (modVO == null)) {
    			it.remove();
    			this.deleteDesignRelation(tempAllocation);
    		}
    		else {     	
    			// Warning: if the responsibility dependencies changed and a responsibility 
    			// has been refined, then it should NOT be allocated to its corresponding module anymore
    			if (responsibilities.isLeaf(resVO)) {
    				this.defineResponsibility(resVO);
    				allocated = this.setResponsibilityAllocation(modVO, resVO, true);
    			}
    			else {
        			it.remove();
        			this.deleteDesignRelation(tempAllocation);    				
    			}
    		}
    	}

		// Step 3: Visit the modules again, deleting those that now 
    	// have no allocated responsibilities (orphan modules)
		ArchEModuleVO definedModuleVO = null;
		boolean removed = false;
    	for (Iterator<ArchEModuleVO> it = rawModuleVOs.iterator(); it.hasNext();) {
    		definedModuleVO = it.next();
			if (this.getCountAllocatedResponsibilities(definedModuleVO) == 0) { 
				// There's no  responsibilities allocated to this module
				// The operation below removes the module from the view 
				it.remove();
				removed |= this.removeModule(definedModuleVO);
			}
    	}
    	
		// Step 4: Recover the module dependencies, but only establish those that 
    	// now make sense based on the allocation of responsibilities    
    	ArchEModuleDependencyRelationVO tempDependency = null;
//    	ArchEModuleVO parentModule = null;
//    	ArchEModuleVO childModule = null;
    	// Step4(bis): Delete all the module dependencies. Anyway, module dependencies will be
    	// re-computed by initializeView() based on the current responsibilities
    	// and responsibility dependencies in the responsibility structure
    	for (Iterator<ArchEModuleDependencyRelationVO> it = rawModuleDependencies.iterator(); it.hasNext();) {
    		tempDependency = it.next();
			it.remove();
			this.deleteDesignRelation(tempDependency);
		}
//    	for (Iterator<ArchEModuleDependencyRelationVO> it = rawModuleDependencies.iterator(); it.hasNext();) {
//    		tempDependency = it.next();
//    		// The method below only sets the dependency, if the two modules exist in 
//    		// the view (some modules may not exist, because they were removed in step 3)
//    		parentModule = tempDependency.getParent();
//    		childModule = tempDependency.getChild();
//    		if(parentModule == null || childModule == null){
//    			it.remove();
//    			this.deleteDesignRelation(tempDependency);
//    		}
//    		else{    			
//    	    	// TODO: Warning, if the responsibility dependencies changed, some module dependencies may be invalid!!!
//        		this.setModuleDependency(tempDependency.getParent(), tempDependency.getChild(), true);
//    		}
//    	}	

		return removed;
	}

	@Override
	// It deletes all the VOs related to the view
	public void delete() throws ArchEException {
		Session openSession = ArchECoreDataProvider.getSessionFactory().getCurrentSession();
		if(openSession != null && openSession.isConnected() && openSession.isOpen()){
			try{
				// Delete the raw modules defined in this view
				rawModuleVOs = this.getModules();
				openSession.delete(rawModuleVOs);
				
				// Delete the allocation and module-dependency relations
				rawModuleDependencies = this.updateModuleDependencyVOs(); // Lazy synchronization of relation VOs
				openSession.delete(rawModuleDependencies);
				rawResponsibilityAllocations = this.updateResponsibilityAllocationVOs(); // Lazy synchronization of relation VOs
				openSession.delete(rawResponsibilityAllocations);
				
			}catch (HibernateException ex){
				throw new ArchEException(ex.getMessage(),ex.getCause());
			}			
		}		
	}

	@Override
	public void restore() throws ArchEException {
		Session openSession = ArchECoreDataProvider.getSessionFactory().getCurrentSession();
		if(openSession != null && openSession.isConnected() && openSession.isOpen()){
			try {				
				this.reset();
			
				// Restore raw components from the component table
		    	Query qModules = ArchECoreDataProvider.getSessionFactory()
		    			.getCurrentSession().createQuery("from ArchEModuleVO as module where module.version = ?");
		    	qModules.setInteger(0, version.getId());
		    	rawModuleVOs = qModules.list();	    
		    	
		    	// Restore the dependency relationships between modules
		    	Query qDependencies = ArchECoreDataProvider.getSessionFactory()
		    			.getCurrentSession().createQuery("from ArchEModuleDependencyRelationVO as rel where rel.version = ?");
		    	qDependencies.setInteger(0, version.getId());
		    	rawModuleDependencies = qDependencies.list();
		    	
		    	// Restore the allocation relationships between those modules and responsibilities
		    	Query qAllocations = ArchECoreDataProvider.getSessionFactory()
    					.getCurrentSession().createQuery("from ArchEResponsibilityToModuleRelationVO as rel where rel.version = ?");
		    	qAllocations.setInteger(0, version.getId());
		    	rawResponsibilityAllocations = qAllocations.list();
		    	
			}catch (HibernateException ex){
				throw new ArchEException(ex.getMessage(),ex.getCause());
			}
		}		
	}

	@Override
	// It saves all the VOs related to the view
	public void save() throws ArchEException {
		super.save();
		
		Session openSession = ArchECoreDataProvider.getSessionFactory().getCurrentSession();
		if(openSession != null && openSession.isConnected() && openSession.isOpen()){
			try{
				// Save or update the raw modules defined in this view
				rawModuleVOs = this.getModules();
				for (Iterator<ArchEModuleVO> it = rawModuleVOs.iterator(); it.hasNext();)
					openSession.saveOrUpdate(it.next());
				
				// Save or update the allocation and module-dependency relations
				rawModuleDependencies = this.updateModuleDependencyVOs(); // Lazy synchronization of relation VOs
				for(Iterator<ArchEModuleDependencyRelationVO> it=rawModuleDependencies.iterator(); it.hasNext() ; )
					openSession.saveOrUpdate(it.next());			

				rawResponsibilityAllocations = this.updateResponsibilityAllocationVOs(); // Lazy synchronization of relation VOs
				for(Iterator<ArchEResponsibilityToModuleRelationVO> it=rawResponsibilityAllocations.iterator(); it.hasNext() ; )
					openSession.saveOrUpdate(it.next());			
				
			
			}catch (HibernateException ex){
				throw new ArchEException(ex.getMessage(),ex.getCause());
			}			
		}		
	}

	@Override
	public void saveAs(ArchEVersionVO newVersion) throws ArchEException {
		Session openSession = ArchECoreDataProvider.getSessionFactory().getCurrentSession();
		if(openSession != null && openSession.isConnected() && openSession.isOpen()){
			try {	
				// Create a copy of the existing modules
				ArchEModuleVO itemMod = null;
				rawModuleVOs = this.getModules();
				for(Iterator<ArchEModuleVO> it = rawModuleVOs.iterator(); it.hasNext();) {
					itemMod = it.next();
					itemMod.setVersion(newVersion);
					openSession.save(itemMod);
				}
				
				// Create a copy of the existing dependency relations
				ArchEModuleDependencyRelationVO itemDep = null;
				rawModuleDependencies = this.updateModuleDependencyVOs(); // Lazy synchronization of relation VOs
				for(Iterator<ArchEModuleDependencyRelationVO> it = rawModuleDependencies.iterator(); it.hasNext();){
					itemDep = it.next();
					itemDep.setVersion(newVersion);
					openSession.save(itemDep);			
				}

				// Create a copy of the existing dependency relations
				ArchEResponsibilityToModuleRelationVO itemAllo = null;
				// Lazy synchronization of relation VOs
				rawResponsibilityAllocations = this.updateResponsibilityAllocationVOs();
				for(Iterator<ArchEResponsibilityToModuleRelationVO> it = rawResponsibilityAllocations.iterator(); it.hasNext();){
					itemAllo = it.next();
					itemAllo.setVersion(newVersion);
					openSession.save(itemAllo);			
				}
				
			}catch (HibernateException ex){
				throw new ArchEException(ex.getMessage(),ex.getCause());
			}			
		}
		
	}
	
//	public ArchEModuleVO findModule(String name) {
//		for (int i = 0; i < countModules; i++) {
//			if (modules[i].getName().equals(name))
//				return (modules[i]);
//		}
//		return (null);
//	}

}


