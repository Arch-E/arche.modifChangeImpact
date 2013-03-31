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
 * Implementation of the change impact analysis model for the modifiability
 * reasoning framework. This analysis model is based on a dependency graph, 
 * constructed out of the module view and the responsibility structure.
 * <p>
 * The main input for the computing dependency graph is a set of 
 * 'primary responsibilities' (responsibilities directly affected by a class 
 * of change, usually coming from a modifiability scenario). Once this input 
 * is provided, the model computes 'derived' responsibility (through responsibility 
 * dependencies), and then computes 'primary modules' (through responsibility 
 * allocations). Note that the this dependency graph doesn't cover always 
 * the whole architecture, but rather it 'scopes' the changes on the architecture 
 * to the'primary modules' and their related responsibilities (a subset of 
 * the whole architecture).
 * <p> 
 * The figures computed as output of the analysis are the following:
 *   - initial cost (before analysis) and estimated cost (after analysis) per   
 *   module and per responsibility
 *   - average initial and final costs for (all)modules and responsibilities
 *   - coupling per responsibility and per module
 *   - average coupling for (all) modules and responsibilities
 *   - average cohesion for (all) modules
 *   - rate of primary modules and primary responsibilities (fraction of the 
 *   whole architecture)
 *  <p>
 *  The basic steps to perform the analysis (from a reasoning framework) are
 *  the following:
 *    1) create an instance of ChangeImpactAnalyzer for the current architecture
 *    (i.e., the module view and the corresponding responsibility structure)
 *    2) set the 'primary responsibilities'
 *    3) call method doInterpretation() to start the analysis
 *    4) access any of the computed values 
 * 
 * @author Andres Diaz-Pace
 */

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import arche.modifChangeImpact.hibernate.vo.ArchEModuleVO;
import arche.modifChangeImpact.hibernate.vo.ArchEResponsibilityDependencyRelationVO;
import edu.cmu.sei.arche.ArchEException;
import edu.cmu.sei.arche.external.data.ArchERelation;
import edu.cmu.sei.arche.external.data.ArchEResponsibility;
import edu.cmu.sei.arche.external.data.ArchEResponsibilityStructure;


public class ChangeImpactAnalyzer {
	
	private static final int MAX_DEPENDENCY_MATRIX 	= 50; // For 'primary' responsibilities
	private static final int MAX_MODULES 			= 50; // For 'primary' modules
	
	// Default costs for responsibilities and modules (accessed also by reasoning framework)
	public static final double DEFAULT_RESPONSIBILITY_COST 					= 7.5;
	public static final double DEPENDENT_RESPONSIBILITY_COST 				= 2.5;
	public static final double DEFAULT_RIPLING_PROBABILITY_RESPONSIBILITIES = 0.45;
	public static final double DEFAULT_MODULE_COST 							= 10;
	public static final double DEPENDENT_MODULE_COST 						= 3;
	
	// Range of values for costs for responsibilities and modules (accessed also by reasoning framework)
	public static final double MIN_RESPONSIBILITY_COST 	= 1;
	public static final double MAX_RESPONSIBILITY_COST 	= 30;
	public static final double MIN_MODULE_COST 			= 1;
	public static final double MAX_MODULE_COST 			= 30;

	///////////////////////////////////////////////////////////////
	// Functions to normalize (and denormalize) costs to the range [0..1] for uniformity
	// of computations
	
	public static double normalizeModuleCost(double cost) {
		double normal = (cost - MIN_MODULE_COST) / (MAX_MODULE_COST - MIN_MODULE_COST);
		return (normal);
	}

	public static double denormalizeModuleCost(double cost) {
		double denormal = cost * (MAX_MODULE_COST - MIN_MODULE_COST)+ MIN_MODULE_COST;
		return (denormal);
	}

	public static double normalizeResponsibilityCost(double cost) {
		double normal = (cost - MIN_RESPONSIBILITY_COST) / (MAX_RESPONSIBILITY_COST - MIN_RESPONSIBILITY_COST);
		return (normal);
	}

	public static double denormalizeResponsibilityCost(double cost) {
		double denormal = cost * (MAX_RESPONSIBILITY_COST - MIN_RESPONSIBILITY_COST)+ MIN_RESPONSIBILITY_COST;
		return (denormal);
	}

	// A predefined utility function, based on the response measure (cost) of a scenario
	private static final double MAX_EXPECTED_VALUE = 2000;
//	public static double getUtility(double response, double referenceResponse, int resources,
//			RFArchitecturalTransformation lastTacticApplied) {
//		
//		double utility = 0.0;		
//		if (response <= referenceResponse) { // The response is below the threshold, so the scenario is met
////			System.out.println("EVALUATING REAL OPTIONS FOR TACTIC: "+lastTacticApplied.getClass().getName()+" maintenanceCost= "+lastTacticApplied.getMaintenanceCost());
//			OptionPricingCalculator opc = new OptionPricingCalculator(lastTacticApplied,true);
//			double value = opc.getTotalOptionValue(resources);
////			System.out.println("________________Option value for n= "+resources+" t= "+resources+" ==> "+value);
//			if (value >= 0) {
//				double b = 0.1;
//				double a = (1.0 - b) / MAX_EXPECTED_VALUE;
//				utility = a * value + b;
//			}			
//			System.out.println("________________Utility ==> "+utility);
//		}
//		
//		// The response is around the reference value
////		if (Math.abs(response - referenceResponse) <= referenceResponse * 0.1)
////			utility = 0.5;
////		else if (response > referenceResponse) // The response exceeds the threshold
////			utility = 0.0;
////		else if ((referenceResponse - response) <= referenceResponse * 0.25)
////			utility = 0.7;
////		System.out.println("COMPUTING UTILITY FOR: "+response+" (reference= "+referenceValue+" ) --> "+utility);
//		return (utility);
//	}

	// References to the module view and associated responsibility structure
	protected RFModuleView moduleView = null;
	protected ArchEResponsibilityStructure allResponsibilities = null;

	// Modules and responsibilities affected by the change. The notion of 'primary' responsibilities 
	// (affected by the change) determines a 'scope' for the change as a subset of the general module view 
	protected ArchEResponsibility[] primaryResponsibilities;
	protected ArchEModuleVO[] primaryModules;
	protected int indexPrimaryResponsibilities;
	protected int indexPrimaryModules;
	protected double[][] respDependencies; // Strength of dependencies between 'primary' responsibilities (only)
	protected double[][] modDependencies; // Strength of dependencies between 'primary' modules (only)
	
	protected boolean needsComputation = false; // Set to true when either input parameters
	// or the module view topology is changed

	//---- Input parameters to the analysis ----
	protected double[] respBasicCosts; // Default cost of changing a 'primary' responsibility
	protected double[] modBasicCosts; // Default cost of changing a 'primary' module	
	

	//---- Dependent/output parameters of the analysis ----
	protected double[] respComputedCosts; // Cost of changing each 'primary' responsibility 
	// (according to the module it belongs to and its neighborhood of responsibilities
	
	protected double[] modComputedCosts; // Cost of changing each 'primary' module 
	// (according to the number of responsibilities allocated to it, and its dependent modules 
	
	protected double[] modCohesion; // Cohesion value for each 'primary' module 
	
	protected double[] modCoupling; // Coupling value for each 'primary' module
	
	public ChangeImpactAnalyzer() {
		this(null,null);
	}

	public ChangeImpactAnalyzer(RFModuleView adl, ArchEResponsibilityStructure respStructure)  {
		moduleView = adl;
		allResponsibilities = respStructure;		
		indexPrimaryResponsibilities = -1;
		indexPrimaryModules = -1;

		primaryResponsibilities = new ArchEResponsibility[MAX_DEPENDENCY_MATRIX];
		respDependencies = new double[MAX_DEPENDENCY_MATRIX][MAX_DEPENDENCY_MATRIX];
		respBasicCosts = new double[MAX_DEPENDENCY_MATRIX];
		respComputedCosts = new double[MAX_DEPENDENCY_MATRIX];
		
		primaryModules = new ArchEModuleVO[MAX_MODULES];
		modDependencies = new double[MAX_MODULES][MAX_MODULES];
		modBasicCosts = new double[MAX_MODULES];
		modComputedCosts = new double[MAX_MODULES];
		modCohesion = new double[MAX_MODULES];
		modCoupling = new double[MAX_MODULES];
		
		this.resetInputParameters();
		this.resetOutputParameters();
		needsComputation = true;
	}
	
	//---- Configuration methods for the analysis ----
	
	/**
	 * Set the module view and the responsibility structure on which the analysis will be performed
	 * 
	 * @param adl The module view
	 * @param respStructure The responsibility structure
	 */
	public void configureArchitecture(RFModuleView adl, ArchEResponsibilityStructure respStructure) {
		moduleView = adl;
		allResponsibilities = respStructure;

		this.resetInputParameters();
		this.resetOutputParameters();
		needsComputation = true;
		return;
	}
	
	/**
	 * Flag that indicates if the analysis need to be computed again (because something may have changed)
	 * 
	 * @return
	 */
	public boolean needsComputation() {
		return (needsComputation);
	}
	
	/**
	 * Calling method means that some modules and responsibilities (as handled by the module view) 
	 * may have changed, their basic costs, or perhaps some of the dependencies or allocations
	 */
	public void setDesignChanged() {
		needsComputation = true;

		return;
	}
	
	/** 
	 * All the input parameters are set to zero, and the flag for
	 * re-computation of the analysis is set to true
	 */ 
	public void resetInputParameters() {
		
		initializeResponsibilityCosts(0.0);
		initializeModuleCosts(0.0);
		indexPrimaryResponsibilities = -1;
		indexPrimaryModules = -1;
		// Note: after this method is invoked, the modules and responsibilities 
		// have to be provided again to the analyzer (as well as their costs)
		
		needsComputation = true;
		
		return;
	}

	/** 
	 * All the output/derived parameters are set to zero, and the flag for 
	 * re-computation of the analysis is set to true
	 */
	public void resetOutputParameters() {
		
		initializeResponsibilityDependencyMatrix(0.0);
		initializeModuleDependencyMatrix(0.0);
		
		initializeResponsibilityComputedCosts(0.0);
		initializeModuleComputedCosts(0.0);
		initializeModuleCohesion(0.0);
		initializeModuleCoupling(0.0);
		
		needsComputation = true;
		
		return;
	}
	
	protected void initializeResponsibilityDependencyMatrix(double value) {
		
		for (int i = 0; i < MAX_DEPENDENCY_MATRIX; i++)
			for (int j = 0; j < MAX_DEPENDENCY_MATRIX; j++)
				respDependencies[i][j] = value;
		
		return;
	}

	protected void initializeModuleDependencyMatrix(double value) {
		
		for (int i = 0; i < MAX_MODULES; i++)
			for (int j = 0; j < MAX_MODULES; j++)
				modDependencies[i][j] = value;
		
		return;
	}

	protected void initializeResponsibilityCosts(double value) {
		
		for (int i = 0; i < MAX_DEPENDENCY_MATRIX; i++)
			respBasicCosts[i] = value;
		
		return;
	}

	protected void initializeResponsibilityComputedCosts(double value) {
		
		for (int i = 0; i < MAX_DEPENDENCY_MATRIX; i++)
			respComputedCosts[i] = value;
		
		return;
	}

	protected void initializeModuleCosts(double value) {
		
		for (int i = 0; i < MAX_MODULES; i++)
			modBasicCosts[i] = value;
		
		return;
	}

	protected void initializeModuleComputedCosts(double value) {
		
		for (int i = 0; i < MAX_MODULES; i++)
			modComputedCosts[i] = value;
		
		return;
	}

	protected void initializeModuleCohesion(double value) {
		
		for (int i = 0; i < MAX_MODULES; i++)
			modCohesion[i] = value;
		
		return;
	}

	protected void initializeModuleCoupling(double value) {
		
		for (int i = 0; i < MAX_MODULES; i++)
			modCoupling[i] = value;
		
		return;
	}

	/** 
	 * This is the main method to compute all the output parameters (however, it doesn't change
	 * the structure of the dependency graph)
	 */ 
	public void doEvaluation() {
		
		this.resetOutputParameters();		

		// These are preparatory computations to calculate the figures
		this.computeChangeProbabilityResponsibilities();
		//this.printResponsibilityDependencies();
		this.computeChangeProbabilityModules();
		//this.printModuleDependencies();

		// These are all the figures estimated by the analyzer (for a given class of change)
		this.estimateCostOfChangePrimaryModules();
		this.estimateCostOfChangePrimaryResponsibilities();
		this.estimateCouplingPrimaryModules();
		this.estimateCohesionPrimaryModules();
		
		//this.printModuleEstimatedCosts();
		
		needsComputation = false;
	}

	protected List<ArchEResponsibility> deriveSecondaryResponsibilitiesFor(ArchEResponsibility primary) {
		
		List<ArchEResponsibility> dependentResps = new ArrayList<ArchEResponsibility>();
		
		String relationTypeVO = ArchEResponsibilityDependencyRelationVO.class.getName();
		List<ArchERelation> dependencies = allResponsibilities.getRelations(relationTypeVO);		
		
		ArchEResponsibilityDependencyRelationVO rel = null;		
		
		for(Iterator<ArchERelation> it = dependencies.iterator(); it.hasNext();) {
			rel = (ArchEResponsibilityDependencyRelationVO)(it.next());
			
			if (rel.getParent().equals(primary) && (!dependentResps.contains(rel.getChild())))
				dependentResps.add(rel.getChild());
			else if (rel.getChild().equals(primary) && (!dependentResps.contains(rel.getParent())))
				dependentResps.add(rel.getParent());
		}
		
		return (dependentResps);
	}

	/** 
	 * This is the method used by the external reasoning framework to set
	 * the responsibilities related to a given class of change as primary 
	 * responsibilities and then run the interpretation of the model
	 * (some other 'inferred' responsibilities and primary modules are automatically 
	 * identified for this input)
	 * 
	 * @param responsibilities the input set of primary responsibilities 
	 * @throws ChangeImpactAnalysisException
	 */
	public boolean doInterpretation(List<ArchEResponsibility> responsibilities) 
									throws ChangeImpactAnalysisException {
		
		// It is assumed that all the responsibilities already exist within the module view
		boolean allOk = true;
		ArchEResponsibility resp = null;		
		
		for (Iterator<ArchEResponsibility> it = responsibilities.iterator(); it.hasNext();) {
			resp = it.next();
			if (moduleView.isAllocated(resp)) 
				this.addPrimaryResponsibility(resp);
		}
		//System.out.println("Primary responsibilities so far: "+(indexPrimaryResponsibilities+1));
		
		// Configure related primary modules
		indexPrimaryModules = -1;
		initializeModuleCosts(0.0);

		List<ArchEModuleVO> listPrimaryModules = this.getRelatedPrimaryModules(responsibilities);
		ArchEModuleVO mod = null;
		for (Iterator<ArchEModuleVO> itModules = listPrimaryModules.iterator(); itModules.hasNext();) {
			mod = itModules.next();
			//System.out.println("--> Adding module: "+mod.getName()+" cost= "+mod.getCostOfChange());
			this.addPrimaryModule(mod);
		}
		//System.out.println("Primary modules so far: "+(indexPrimaryModules+1));

		// It adds a number of "dependent" responsibilities to the scope of primary responsibilities
		//double costResp = normalizeResponsibilityCost(MIN_RESPONSIBILITY_COST);
		//double costResp = normalizeResponsibilityCost(DEFAULT_RESPONSIBILITY_COST);
		double costResp = normalizeResponsibilityCost(DEPENDENT_RESPONSIBILITY_COST);
		List<ArchEResponsibility> secondaryResps = this.getDependentResponsibilities(responsibilities);	
		for (Iterator<ArchEResponsibility> it = secondaryResps.iterator(); it.hasNext();) {
			resp = it.next();
			if (!this.isPrimaryResponsibility(resp))
				this.addPrimaryResponsibility(resp,costResp);
		}
		//System.out.println("Primary responsibilities with dependents: "+(indexPrimaryResponsibilities+1));

		listPrimaryModules = this.getRelatedPrimaryModules();
		double costOfChange = 0.0;
		for (Iterator<ArchEModuleVO> itModules = listPrimaryModules.iterator(); itModules.hasNext();) {
			mod = itModules.next();
			// Normalization of the cost to the interval [0..1]
			//costOfChange = normalizeModuleCost(MIN_MODULE_COST);
			//costOfChange = normalizeModuleCost(DEFAULT_MODULE_COST);
			//costOfChange = normalizeModuleCost(DEPENDENT_MODULE_COST);
			costOfChange = normalizeModuleCost(mod.getCostOfChange());
			if (!this.isPrimaryModule(mod)) 
				this.addPrimaryModule(mod,costOfChange);
		}
		//System.out.println("Primary modules finally: "+(indexPrimaryModules+1));

		// Configure related (or inferred) primary responsibilities (because they 
		// are inside each modules marked as primary)
		ArchEResponsibility inferredPrimary = null;
		//costResp = normalizeResponsibilityCost(MIN_RESPONSIBILITY_COST);
		//costResp = normalizeResponsibilityCost(DEFAULT_RESPONSIBILITY_COST);
		costResp = normalizeResponsibilityCost(DEPENDENT_RESPONSIBILITY_COST);
		for (Iterator<ArchEResponsibility> it = allResponsibilities.getResponsibilities().iterator(); it.hasNext();) {
			inferredPrimary = it.next();
			if (!this.isPrimaryResponsibility(inferredPrimary)) {
				for (int i = 0; i <= indexPrimaryModules; i++) {
					if (moduleView.isAllocated(inferredPrimary, primaryModules[i]) 
							&& (!this.isPrimaryResponsibility(inferredPrimary)))
						this.addPrimaryResponsibility(inferredPrimary,costResp);
				}					
			}
		}
		//System.out.println("Primary responsibilities with inferred: "+(indexPrimaryResponsibilities+1));

		// Note here that now all the strength dependencies between responsibilities
		// and modules need to be recomputed
		needsComputation = true;
		return (allOk);
	}

	private List<ArchEResponsibility> getDependentResponsibilities(List<ArchEResponsibility> responsibilities) {
		// It adds a number of "dependent" responsibilities to the scope of primary responsibilities
		List<ArchEResponsibility> dependents = new ArrayList<ArchEResponsibility>();
		ArchEResponsibility resp = null;
		ArchEResponsibility temp = null;
		for (Iterator<ArchEResponsibility> it = responsibilities.iterator(); it.hasNext();) {
			resp = it.next();
			for(Iterator<ArchEResponsibility> itSec = deriveSecondaryResponsibilitiesFor(resp).iterator(); itSec.hasNext();) {
				temp = itSec.next();
				if (!responsibilities.contains(temp) && !dependents.contains(temp))
					dependents.add(temp);
			}
		}
		return (dependents);
	}

	protected List<ArchEModuleVO> getRelatedPrimaryModules(List<ArchEResponsibility> responsibilities) { 
		
		List<ArchEModuleVO> primaryModules = new ArrayList<ArchEModuleVO>();
		ArchEResponsibility resp = null;
		ArchEModuleVO mod = null;
		List<ArchEModuleVO> primaryModulesResp = null;
		for (Iterator<ArchEResponsibility> itResps = responsibilities.iterator(); itResps.hasNext(); ) {
			resp = itResps.next();
			primaryModulesResp = moduleView.getModulesByResponsibility(resp);
			for (Iterator<ArchEModuleVO> itMods = primaryModulesResp.iterator(); itMods.hasNext();) {
				mod = itMods.next();
				if (!primaryModules.contains(mod))
					primaryModules.add(mod);
			}
		}

		return (primaryModules);
	}
	
	protected List<ArchEResponsibility> getInferredResponsibilities(List<ArchEResponsibility> responsibilities, List<ArchEModuleVO> modules) {
		List<ArchEResponsibility> inferredResponsibilities = new ArrayList<ArchEResponsibility>();
		ArchEResponsibility inferredPrimary = null;
		for (Iterator<ArchEResponsibility> itResps = allResponsibilities.getResponsibilities().iterator(); itResps.hasNext();) {
			inferredPrimary = itResps.next();
			if (!responsibilities.contains(inferredPrimary)) {
				for (Iterator<ArchEModuleVO> itMods = modules.iterator(); itMods.hasNext();) {
					if (moduleView.isAllocated(inferredPrimary, itMods.next()) 
							&& (!inferredResponsibilities.contains(inferredPrimary)))
						inferredResponsibilities.add(inferredPrimary);
				}					
			}
		}
		return (inferredResponsibilities);
	}
	
	/** 
	 * This method adds a primary responsibility for analysis with a particular cost 
	 * (for a given class of change)
	 * 
	 * @param responsibility primary responsibility
	 * @param cost cost of change to set for that responsibility 
	 * @throws ChangeImpactAnalysisException
	 */
	public boolean addPrimaryResponsibility(ArchEResponsibility responsibility, double cost) 
										throws ChangeImpactAnalysisException {
		if (indexPrimaryResponsibilities == MAX_DEPENDENCY_MATRIX - 1) {
			throw (new ChangeImpactAnalysisException("Responsibility matrix is full (size= "+indexPrimaryResponsibilities+1+" )"));
			//return (false); // The matrix is full
		}
		
		int pos = this.getPrimaryResponsibilityIndex(responsibility);
		
		boolean added = false;
		if (pos == -1)  { // The responsibility is a new primary responsibility
			indexPrimaryResponsibilities++;
			pos = indexPrimaryResponsibilities;
			primaryResponsibilities[pos] = responsibility;
			added = true;
		}

		// The cost is updated for the primary responsibility
		respBasicCosts[pos] = cost;
		respComputedCosts[pos] = 0.0;
		
		// The strength dependencies with other primary responsibilities are initialized
		for (int i = 0; i <= indexPrimaryResponsibilities; i++)
			respDependencies[pos][i] = 0.0;
		for (int i = 0; i <= indexPrimaryResponsibilities; i++)
			respDependencies[i][pos] = 0.0;
		respDependencies [pos][pos] = 1.0;
		
		needsComputation = true;
		
		return (added);
	}
	
	/** 
	 * This method adds a primary responsibility for analysis with a default cost 
	 * (for a given class of change) of with the cost associated to the responsibility
	 * as a parameter
	 * 
	 * @param responsibility primary responsibility
	 * @throws ChangeImpactAnalysisException	 * 
	 */
	protected boolean addPrimaryResponsibility(ArchEResponsibility responsibility) 
								throws ChangeImpactAnalysisException {
		try {
			double costOfChange = responsibility.getDoubleParameter(ModifChangeImpactReasoningFramework.PARAMETER_COST_OF_CHANGE);
			// Normalization of the cost to the interval [0..1]
			//costOfChange = DEFAULT_RESPONSIBILITY_COST;
			costOfChange = normalizeResponsibilityCost(costOfChange);
			boolean addedOk = this.addPrimaryResponsibility(responsibility, costOfChange);
			return (addedOk);
		} catch (ArchEException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		return (false);
	}
	
	protected List<ArchEModuleVO> getRelatedPrimaryModules() { 
		// The existing modules are discarded
		//indexPrimaryModules = -1;
		//initializeModuleCosts(0.0);
		
		List<ArchEModuleVO> primaryModules = new ArrayList<ArchEModuleVO>();
		ArchEResponsibility resp = null;
		ArchEModuleVO mod = null;
		List<ArchEModuleVO> primaryModulesResp = null;
		//boolean addedOk = false;
		//double costOfChange = 0;
		for (int i = 0; i <= indexPrimaryResponsibilities; i++) {
			resp = primaryResponsibilities[i];
			primaryModulesResp = moduleView.getModulesByResponsibility(resp);
			for (Iterator<ArchEModuleVO> it = primaryModulesResp.iterator(); it.hasNext();) {
				mod = it.next();
				// Normalization of the cost to the interval [0..1]
				//costOfChange = normalizeModuleCost(mod.getCostOfChange());
				//costOfChange = normalizeModuleCost(DEFAULT_MODULE_COST);
				//addedOk = this.setPrimaryModule(mod,costOfChange);
				if (!primaryModules.contains(mod))
					primaryModules.add(mod);
			}
		}

		return (primaryModules);
	}

	/**
	 * Add a 'primary module' with a specific cost
	 * 
	 * @param module The module being added
	 * @param cost The cost of change for the module
	 * @exception ChangeImpactAnalysisException In case there's no room to add the module
	 */
	public boolean addPrimaryModule(ArchEModuleVO module, double cost) 
								throws ChangeImpactAnalysisException {
		if (indexPrimaryResponsibilities == MAX_MODULES - 1) {
			throw (new ChangeImpactAnalysisException("Component matrix is full (size= "+(indexPrimaryModules+1)+" )"));
			//return (false); // The matrix is full
		}

		int pos = this.getPrimaryModuleIndex(module);		
		boolean added = false;
		if (pos == -1) { // The module is a new primary module
			indexPrimaryModules++;
			pos = indexPrimaryModules;
			primaryModules[pos] = module;
			added = true;
		}

		// The cost is updated for the primary module
		modBasicCosts[pos] = cost;
		
		// The strength dependencies with other primary modules are initialized
		for (int i = 0; i <= indexPrimaryModules; i++)
			modDependencies[pos][i] = 0.0;
		for (int i = 0; i <= indexPrimaryModules; i++)
			modDependencies[i][pos] = 0.0;
		modDependencies [pos][pos] = 1.0;	
	
		return (added);	
	}
	
	protected boolean addPrimaryModule(ArchEModuleVO module) throws ChangeImpactAnalysisException { 
		double costOfChange = module.getCostOfChange();
		// Normalization of the cost to the interval [0..1]
		//costOfChange = DEFAULT_RESPONSIBILITY_COST;
		costOfChange = normalizeModuleCost(costOfChange);
		boolean addedOk = this.addPrimaryModule(module, costOfChange);
		return (addedOk);
	}

	/**
	 * Return true if the module is marked as 'primary module'
	 * 
	 * @param module The reference module
	 * @return
	 */
	public boolean isPrimaryModule(ArchEModuleVO module) {

		int pos = this.getPrimaryModuleIndex(module);
		return ((pos >= 0) && (pos <= indexPrimaryModules));
	}

	/**
	 * Return true if the responsibility is marked as 'primary module'
	 * 
	 * @param responsibility The responsibility module
	 * @return
	 */
	public boolean isPrimaryResponsibility(ArchEResponsibility responsibility) {

		int pos = this.getPrimaryResponsibilityIndex(responsibility);
		return ((pos >= 0) && (pos <= indexPrimaryResponsibilities));
	}

	protected int getPrimaryResponsibilityIndex(ArchEResponsibility responsibility) {
		for (int i = 0; i <= indexPrimaryResponsibilities; i++) {
			if (primaryResponsibilities[i].equals(responsibility))
				return (i);
			// The two responsibilities are equal if  they have the same name
			// (under the same version of the architecture)
		}
		return (-1);
	}

	protected int getPrimaryModuleIndex(ArchEModuleVO module) {
		for (int i = 0; i <= indexPrimaryModules; i++) {
			if (primaryModules[i].equals(module))
				return (i);
			// The two modules are equal if  they have the same name
			// (under the same version of the architecture)
		}
		return (-1);
	}

	//---- Estimation of output/dependent parameters of components and responsibilities ----
	
	/** 
	 * This method gives an estimate of the rippling of change (or strength of dependency)
	 *  between pairs of primary responsibilities
	 *   - rule 1: if two responsibilities have a dependency and they are also
	 *	           allocated to the same module, rippling = 1.0
	 *   - rule 2: if two responsibilities don't have a dependency, rippling = 0.0
	 *   - rule 3: if the responsibilities have a dependency but they are in different
	 *			   modules, rippling = function(Rij outgoingProbability parameter, Rji incomingProbability parameter)
	 * Note: It needs to be recomputed after changing the allocation of responsibilities
	 * or after changing the dependencies among responsibilities
	 */
	protected void computeChangeProbabilityResponsibilities() {
		
		ArchEResponsibility resp1 = null;		
		ArchEResponsibility resp2 = null;
		//double ripplingValue;
		
		for (int i = 0; i <= indexPrimaryResponsibilities; i++) {
			resp1 = primaryResponsibilities[i];
			
			for (int j = i+1; j <= indexPrimaryResponsibilities; j++) {
				resp2 = primaryResponsibilities[j];				
				
				if (moduleView.areCoAllocated(resp1, resp2)) { // Rule 1
					respDependencies[i][j] = 1.0;
					respDependencies[j][i] = 1.0;					
				}
				else {
					String relationTypeVO = ArchEResponsibilityDependencyRelationVO.class.getName();
					ArchERelation depIJ = allResponsibilities.getRelation(resp1, resp2, relationTypeVO);
					respDependencies[i][j] = this.getOutgoingRipplingProbability(depIJ);
					respDependencies[j][i] = this.getIncomingRipplingProbability(depIJ);										
//					if (depIJ != null) { // Rule 3
//						try {
//							//ripplingValue = Math.random()*DEFAULT_RIPLING_PROBABILITY_RESPONSIBILITIES;
//							//ripplingValue = this.calculateRipplingProbability(depIJ);
//							respDependencies[i][j] = depIJ.getDoubleParameter(ModifChangeImpactReasoningFramework.PARAMETER_PROBABILITY_OUTGOING);
//							respDependencies[j][i] = depIJ.getDoubleParameter(ModifChangeImpactReasoningFramework.PARAMETER_PROBABILITY_INCOMING);										
//						} catch (ArchEException e) {
//							// TODO Auto-generated catch block
//							e.printStackTrace();
//						}						
//					}
//					else { // Rule 2
//						respDependencies[i][j] = 0.0;
//						respDependencies[j][i] = 0.0;														
//					}					
				}
				
			}
		}
		
		// Note: Someone may alter (later) these probabilities if needed 
		return;
	}

	protected double getIncomingRipplingProbability(ArchERelation dependencyAB) {	
		double rippling = 0.0;
		if (dependencyAB != null) {
			try {
				rippling = dependencyAB.getDoubleParameter(ModifChangeImpactReasoningFramework.PARAMETER_PROBABILITY_INCOMING);
			} catch (ArchEException e1) {
				// TODO Auto-generated catch block
				e1.printStackTrace();
			}
		}
		return (rippling);
	}

	protected double getOutgoingRipplingProbability(ArchERelation dependencyAB) {
		double rippling = 0;
		if (dependencyAB != null) {
			try {
				rippling = dependencyAB.getDoubleParameter(ModifChangeImpactReasoningFramework.PARAMETER_PROBABILITY_OUTGOING);
			} catch (ArchEException e1) {
				// TODO Auto-generated catch block
				e1.printStackTrace();
			}
		}
		return (rippling);
	}

//	private double calculateRipplingProbability(ArchERelation dependencyAB) {
//		double rippling = 0;
//		try {
//			double ripplingABIncoming = dependencyAB.getDoubleParameter(ModifChangeImpactReasoningFramework.PARAMETER_PROBABILITY_INCOMING);
//			double ripplingABOutgoing = dependencyAB.getDoubleParameter(ModifChangeImpactReasoningFramework.PARAMETER_PROBABILITY_OUTGOING);
//		
//			rippling = ( ripplingABIncoming + ripplingABOutgoing ) / 2;
//
//		} catch (ArchEException e) {
//			// TODO Auto-generated catch block
//			e.printStackTrace();
//		}
//		return (rippling);		
//	}
	
	/** 
	 * This method gives an estimate of the rippling of change (or strength of the dependency)
	 * between pairs of primary modules
	 *  - rule 1: if two components do not have a dependency, rippling = 0.0
	 *  - rule 2: if two components do have a dependency, rippling = average rippling
	 *            of those responsibilities allocated to the two components 
	 * Note: it needs to be recomputed after executing 
	 * computeChangeProbabilityResponsibilities (above) or after changing the 
	 * rippling probabilities  in the responsibilities
	 */
	protected void computeChangeProbabilityModules() {
		
		ArchEModuleVO mod1 = null;
		ArchEModuleVO mod2 = null;
		double dependencyIJ = 0.0;
		double dependencyJI = 0.0;
		
		for (int i = 0; i <= indexPrimaryModules; i++){
			mod1 = primaryModules[i];
			
			for (int j = i+1; j <= indexPrimaryModules; j++) {
				mod2 = primaryModules[j];
				
				if (moduleView.hasDependency(mod1, mod2)) {
					dependencyIJ = this.getAvgChangeOutgoingProbability(mod1,mod2); // see method below
					dependencyJI = this.getAvgChangeIncomingProbability(mod1,mod2); // see method below
				}
				else {
					dependencyIJ = 0.0;
					dependencyJI = 0.0;
				}

				modDependencies[i][j] = dependencyIJ;
				modDependencies[j][i] = dependencyJI;
				
			}
		}
		
		// Note: Someone may alter (later) these probabilities if needed 
		return;
	}
	
	/** 
	 * This returns an average of the outgoing rippling between two modules, due to all the possible
	 * pairs of responsibilities that connect the two modules
	 */
	private double getAvgChangeOutgoingProbability(ArchEModuleVO mod1, ArchEModuleVO mod2) {
		
		double value = 0;
		int count = 0;
		ArchEResponsibility resp1 = null;
		ArchEResponsibility resp2 = null;
		
		String relationTypeVO = ArchEResponsibilityDependencyRelationVO.class.getName();
		for (int i = 0; i <= indexPrimaryResponsibilities; i++){
			resp1 = primaryResponsibilities[i];
			
			for (int j = i+1; j <= indexPrimaryResponsibilities; j++) {
				resp2 = primaryResponsibilities[j];
				
				if (allResponsibilities.existRelation(resp1, resp2, relationTypeVO)) {
					// If resp1 belong to mod1 and resp2 belongs to mod2
					if (moduleView.isAllocated(resp1, mod1) && moduleView.isAllocated(resp2, mod2)) {
						value = value + respDependencies[i][j];
						count++;
					} // or vice versa
					else if (moduleView.isAllocated(resp2, mod1) && moduleView.isAllocated(resp1, mod2)) {
						value = value + respDependencies[j][i];
						count++;
					}	
				}
			}
		}
		
		if (count > 0)
			value = value / count;
		
		return (value);
	}

	/** 
	 * This returns an average of the incoming rippling between two modules, due to all the possible
	 * pairs of responsibilities that connect the two modules
	 */
	private double getAvgChangeIncomingProbability(ArchEModuleVO mod1, ArchEModuleVO mod2) {
		
		double value = 0;
		int count = 0;
		ArchEResponsibility resp1 = null;
		ArchEResponsibility resp2 = null;
		
		String relationTypeVO = ArchEResponsibilityDependencyRelationVO.class.getName();
		for (int i = 0; i <= indexPrimaryResponsibilities; i++){
			resp1 = primaryResponsibilities[i];
			
			for (int j = i+1; j <= indexPrimaryResponsibilities; j++) {
				resp2 = primaryResponsibilities[j];
				
				if (allResponsibilities.existRelation(resp1, resp2, relationTypeVO)) {
					// If resp1 belong to mod1 and resp2 belongs to mod2
					if (moduleView.isAllocated(resp1, mod1) && moduleView.isAllocated(resp2, mod2)) {
						value = value + respDependencies[j][i];
						count++;
					} // or vice versa
					else if (moduleView.isAllocated(resp2, mod1) && moduleView.isAllocated(resp1, mod2)) {
						value = value + respDependencies[i][j];
						count++;
					}	
				}
			}
		}
		
		if (count > 0)
			value = value / count;
		
		return (value);
	}

	/** 
	 * This method estimates the cost of changing a 'primary' module PM, based on 
	 * the default module cost of M, the cost of responsibilities allocated to PM, 
	 * and the  change rippling probability of any module dependent upon PM
	 *   - cost(PMi) = defaultCost(PMi) 
	 *							+ n * (AVERAGE Ripplingji * CostDependentModulesj)
	 *							+ k * (AVERAGE costAllocatedResponsibilities) 
	 * cost(PMi) should be a value between 0.0 and 1.0 (maximum cost)
	 * Precondition: this computation should be invoked after all the dependencies 
	 * among modules and among responsibilities have been updated (e.g., see consistency checking)
	 */
	protected void estimateCostOfChangePrimaryModules() {
		
		double costNeighbors = 0.0;
		double costAllocatedResponsibilities = 0.0;
		double count = 0;		
		ArchEResponsibility resp = null;
		
		//System.out.println("++++++Estimated costs: "+(indexPrimaryModules+1)+" modules");
		for (int i = 0; i <= indexPrimaryModules; i++) {
			
			// This part is for the cost of adjacent modules
			count = 0;
			costNeighbors = 0.0;
			for (int j = 0; j <= indexPrimaryModules; j++) {
				if ((modDependencies[j][i] > 0) && (i != j)) {
					costNeighbors = costNeighbors + modDependencies[j][i] * modBasicCosts[j];
					count++;					
				}
			}
			if (count > 0)
				costNeighbors = costNeighbors / count;
			
			// This part is for the cost of allocated responsibilities
			costAllocatedResponsibilities = 0.0;
			count = 0;
			for (int k = 0; k <= indexPrimaryResponsibilities; k++) {
				resp = primaryResponsibilities[k];
				if (moduleView.isAllocated(resp, primaryModules[i])) {
					costAllocatedResponsibilities = costAllocatedResponsibilities + respBasicCosts[k];
					count++;
				}
			}
			if (count > 0)
				costAllocatedResponsibilities = costAllocatedResponsibilities / count;
			
			double ratio = count / allResponsibilities.getResponsibilities().size();
			modComputedCosts[i] = ratio*modBasicCosts[i] + 0.35*costNeighbors + 0.35*costAllocatedResponsibilities;
//			System.out.println("Estimated cost for: "+primaryModules[i].getName()+" ==> ratioBasiCost "+ratio*modBasicCosts[i]+" costNeighbors "+0.35*costNeighbors+" costAllocation "+0.35*costAllocatedResponsibilities+"  = "+modComputedCosts[i]);
			if (modComputedCosts[i] > 1)
				modComputedCosts[i] = 1.0;
		
		}
		
		// Note: Someone may alter (later) the cost of changing modules if needed 
		//System.out.println("++++++++++++++");
		return;		
	}
	
	/** 
	 * This method estimates the cost of changing a 'primary' responsibility PR, considering 
	 * also the cost(s) of the module(s) the responsibility PR has been allocated to (note
	 * that the dependencies of PR with other responsibilities is not used here)
	 *   - cost(PRi) = defaultCost(PRi) + k * (AVERAGE CostAllocatedModules ) 
	 * cost(PRi) should be a value between 0.0 and 1.0 (maximum cost)
	 * Precondition: this computation should be invoked after all the dependencies 
	 * have been allocated (e.g., see consistency checking)
	 */
	protected void estimateCostOfChangePrimaryResponsibilities() {
		
		double allocationCost = 0.0;
		int count = 0;		
		for (int i = 0; i <= indexPrimaryResponsibilities; i++) {		
		
			allocationCost = 0.0;
			count = 0;
			for (int j = 0; j <= indexPrimaryModules; j++) {
				if (moduleView.isAllocated(primaryResponsibilities[i], primaryModules[j])) {
					allocationCost = allocationCost + modBasicCosts[j];
					count++;
				}
			}
			if (count > 0) 
				allocationCost = allocationCost / count;
						
			// Having indexPrimaryModule == -1 is unlikely, unless there's no primary components at all
			// (which would mean either that there's no primary responsibilities or that they haven't been allocated)
			if(indexPrimaryModules > -1) 
				respComputedCosts[i] = respBasicCosts[i] + 0.8* (count / (indexPrimaryModules+1)) * allocationCost;
			if (respComputedCosts[i] > 1.0)
					respComputedCosts[i] = 1.0;
		}		
	
		// Note: Someone may alter (later) the cost of changing responsibilities if needed 
		return;
	}
	
	/** 
	 * This method estimates the coupling of a 'primary' module PM, taking
	 * the average of dependencies of PM with other primary modules
	 * The average coupling for PM should be a value between 0.0 and 1.0 (maximum coupling)
	 * Note: it needs to be recomputed in the case of modifications in the 
	 * probability of change propagation among components
	 */
	protected void estimateCouplingPrimaryModules() {
		
		double value = 0.0;
		double count = 0;
		for (int i = 0; i <= indexPrimaryModules; i++) {
			
			value = 0.0;
			count = 0;
			for (int j = 0; j <= indexPrimaryModules; j++) {
				if ((modDependencies[i][j] > 0) && (i != j)){
					value = value + modDependencies[i][j] + modDependencies[j][i];
					count = count + 2;
				}
			}

			if (count > 0) 
				value = value / count;

			// Maybe the average of rippling is not the best measure for coupling, because
			// a module may have few module dependencies with high probability of rippling and vice versa
			double connectionRatio = 0.0;
			if ((indexPrimaryModules >= 0) && (count > 2))
				connectionRatio = count / (indexPrimaryModules + 1); 
			
			// This means that the higher the connectionRatio the higher the coupling index
			modCoupling[i] = value + connectionRatio * 0.4; 
			if (modCoupling[i] > 1.0)
				modCoupling[i] = 1.0;		
		}
		
		return;
	}
	
	/** 
	 * This method estimates the cohesion of a 'primary' module PM, based
	 * on the number of responsibilities allocated to the module and on which
	 * of them actually have a 'functional' dependency (internal coupling)
	 * The cohesion for PM should be a value between 0.0 and 1.0 (maximum cohesion)
	 * Precondition: This computation assumes that the coupling of the primary modules
	 * has been already computed
	 */
	protected void estimateCohesionPrimaryModules() {
		
		double countInternalCoupling = 0;
		double countCoAllocation = 0;
		ArchEResponsibility resp1 = null;
		ArchEResponsibility resp2 = null;
		
		for (int i = 0; i <= indexPrimaryModules; i++) {
			countInternalCoupling = 0;
			countCoAllocation = 0;
			
			// It considers all pairs of primary responsibilities
			for (int j = 0; j <= indexPrimaryResponsibilities; j++) {
				resp1 = primaryResponsibilities[j];
				
				for (int k = j+1; k <= indexPrimaryResponsibilities; k++) {
					resp2 = primaryResponsibilities[k];
					
					// If the two responsibilities belong to the module
					if (moduleView.areCoAllocated(primaryModules[i], resp1, resp2)) {
						countCoAllocation = countCoAllocation + 2; // This is a 'casual' coupling between responsibilities
						String relationTypeVO = ArchEResponsibilityDependencyRelationVO.class.getName();
						if (allResponsibilities.existRelation(resp1, resp2, relationTypeVO)) 
							// This is a 'functional' coupling between responsibilities
							// (functional coupling is usually stronger than causal coupling due to the actual allocation)
							countInternalCoupling = countInternalCoupling + 2;								
					}					
				}
			}	
			
			double rateCasualFunctionalCoupling = 0.0;			
			if (countCoAllocation == 0) // The module has only 1 primary responsibility
				rateCasualFunctionalCoupling = 1.0;					
			else if (countInternalCoupling == 0)  // The module has only 'casual' coupling
					rateCasualFunctionalCoupling = 0.5;					
			else rateCasualFunctionalCoupling = (countInternalCoupling / countCoAllocation );

			// We also use the coupling of the module (previously computed)
			modCohesion[i] = rateCasualFunctionalCoupling - modCoupling[i] * 0.2;					
			if (modCohesion[i] < 0)
				modCohesion[i] = 0.0;
		}
		
		return;
	}
	
	// For debugging purposes
	public void printModuleDependencies() {
		
		System.out.println("Matrix of dependencies among modules");
		for (int i = 0; i <= indexPrimaryModules; i++)
			for (int j = 0; j <= indexPrimaryModules; j++)
				System.out.println(" i= "+i+" j="+j+" valueMatrix= "+modDependencies[i][j]);
		
		return;
	}

	// For debugging purposes
	public void printModuleEstimatedCosts() {
		
		System.out.println("Vector of estimated costs and coupling for modules");
		for (int i = 0; i <= indexPrimaryModules; i++) {
			System.out.println("module= "+primaryModules[i].getName()+" i= "+i+" estimatedCost= "+modComputedCosts[i]+" coupling= "+modCoupling[i]);
			System.out.println("denormalized module= "+primaryModules[i].getName()+" i= "+i+" estimatedCost= "+ChangeImpactAnalyzer.denormalizeModuleCost(modComputedCosts[i]));
		}
		
		return;
	}

	// For debugging purposes 
	public void printResponsibilityDependencies() {
		
		System.out.println("Matrix of dependencies among responsibilities");
		for (int i = 0; i <= indexPrimaryResponsibilities; i++)
			for (int j = 0; j <= indexPrimaryResponsibilities; j++)
				System.out.println(" i= "+i+" j="+j+" valueMatrix= "+respDependencies[i][j]);
		
		return;
	}

	//---- Output parameters of the analysis ----
	
	public double getResponsibilityInitialCost(ArchEResponsibility responsibility) {
		
		int pos = this.getPrimaryResponsibilityIndex(responsibility);
		if (pos != -1) // The responsibility is a primary one
			return (denormalizeResponsibilityCost(respBasicCosts[pos]));
		else // The responsibility is any other responsibility in the module view
			return (DEFAULT_RESPONSIBILITY_COST);
	}
	
	public double getResponsibilityEstimatedCost(ArchEResponsibility responsibility) {
		// If no parameter is provided, the value is returned denormalized
		return (getResponsibilityEstimatedCost(responsibility, true));
	}

	public double getResponsibilityEstimatedCost(ArchEResponsibility responsibility, boolean denormalized) {
		
		int pos = this.getPrimaryResponsibilityIndex(responsibility);
		if (pos != -1) { // The responsibility is a primary one
			if (denormalized)
				return (denormalizeResponsibilityCost(respComputedCosts[pos]));
			else return (respComputedCosts[pos]);
		}
		else // The responsibility is any other responsibility in the module view
			return (0.0);
	}

	public double getModuleInitialCost(ArchEModuleVO ArchEResponsibility) {
		
		int pos = this.getPrimaryModuleIndex(ArchEResponsibility);
		if (pos != -1) // The module is a primary one
			return (denormalizeModuleCost(modBasicCosts[pos]));
		else // The module is any other module in the module view
			return (DEFAULT_MODULE_COST);
	}

	public double getModuleEstimatedCost(ArchEModuleVO module) {
		
		int pos = this.getPrimaryModuleIndex(module);
		if (pos != -1) // The module is a primary one
			return (denormalizeModuleCost(modComputedCosts[pos]));
		else // The module is any other module in the module view
			return (0.0);
	}

	/** 
	 * This output parameter considers the average cost of primary responsibilities only, 
	 * and assumes a zero cost for all the remaining responsibilities within the module view
	 */
	public double getAvgResponsibilityInitialCost() {

		double total = 0.0;
		for (int i = 0; i <= indexPrimaryResponsibilities; i++) 
			total = total + respBasicCosts[i];
		
		//int n = moduleView.getCountAllocatedResponsibilities();
		int n = allResponsibilities.getResponsibilities().size(); 
		double costFactor = normalizeResponsibilityCost(DEFAULT_RESPONSIBILITY_COST);
		total = total + costFactor * (n-(indexPrimaryResponsibilities +1));
		if (n > 0)
			total = total / n;
		
		return (denormalizeResponsibilityCost(total));
	}

	/** 
	 * This output parameter considers the average cost of primary modules only, 
	 * and assumes a zero cost for all the remaining responsibilities within the module view
	 */
	public double getAvgModuleInitialCost() {
		
		double total = 0.0;
		for (int i = 0; i <= indexPrimaryModules; i++) {
			total = total + modBasicCosts[i];
		}
		int n = moduleView.getModules().size();
		double costFactor = normalizeModuleCost(DEFAULT_MODULE_COST);
		total = total + costFactor * (n-(indexPrimaryModules +1));
		if (n > 0)
			total = total / n;

		return (denormalizeModuleCost(total));
	}

	/** 
	 * This output parameter considers the average 'computed' cost of primary 
	 * responsibilities, and assumes a zero cost for all the remaining 
	 * responsibilities within the module view
	 * Precondition: This method should be invoked after 
	 * calling method estimateCostOfPrimaryResponsibilities()
	 */
	public double getAvgResponsibilityEstimatedCost() {
		// If no parameter is provided, the value is returned denormalized
		return (getAvgResponsibilityEstimatedCost(true));
	}

	public double getAvgResponsibilityEstimatedCost(boolean denormalized) {
		//this.estimateResponsibilityCosts();
		
		double total = 0.0;
		for (int i = 0; i <= indexPrimaryResponsibilities; i++) 
			total = total + respComputedCosts[i];

		//int n = moduleView.getCountAllocatedResponsibilities();
		int n = allResponsibilities.getResponsibilities().size(); 
		double costFactor = normalizeResponsibilityCost(DEFAULT_RESPONSIBILITY_COST);
		total = total + costFactor * (n-(indexPrimaryResponsibilities +1));
		if (n > 0)
			total = total / n;
		if (denormalized)
			return (denormalizeResponsibilityCost(total));
		else
			return (total);
	}

	/** 
	 * This output parameter considers the average cost of primary modules, 
	 * and assumes a zero cost for all the remaining modules within the module view
	 * Precondition: This method should be invoked after 
	 * calling method estimateCostOfPrimaryModules()
	 */
	public double getAvgModuleEstimatedCost() {
		
		double total = 0.0;
		for (int i = 0; i <= indexPrimaryModules; i++) 
			total = total + modComputedCosts[i];
		
		int n = moduleView.getModules().size();
		double costFactor = normalizeModuleCost(DEFAULT_MODULE_COST);
		total = total + costFactor * (n-(indexPrimaryModules +1));
		if (n > 0)
			total = total / n;
		
		return (denormalizeModuleCost(total));
	}

	/**
	 * This is typically the result of the modifiability analysis. This cost
	 * considers only the sum of all the costs of the individual modules 
	 * 
	 * @return
	 */
	public double getTotalCost() {
		
		double totalModules = 0.0;
		for (int i = 0; i <= indexPrimaryModules; i++) 
			totalModules = totalModules + modComputedCosts[i];	
		//int n = moduleView.getModules().size();
		//double costFactorModules = normalizeModuleCost(DEFAULT_MODULE_COST);
		//totalModules = totalModules + costFactorModules * (n-(indexPrimaryModules +1));

		totalModules = denormalizeModuleCost(totalModules);

		double totalResps = 0.0;
//		for (int i = 0; i <= indexPrimaryResponsibilities; i++) 
//			totalResps = totalResps + respComputedCosts[i];
//		int m = allResponsibilities.getResponsibilities().size(); 
//		double costFactorResps = (DEFAULT_RESPONSIBILITY_COST - MIN_RESPONSIBILITY_COST) / (MAX_RESPONSIBILITY_COST - MIN_RESPONSIBILITY_COST);
//		totalResps = totalResps + costFactorResps * (m-(indexPrimaryResponsibilities +1));
//		totalResps = totalResps * (MAX_RESPONSIBILITY_COST - MIN_RESPONSIBILITY_COST)+ MIN_RESPONSIBILITY_COST;
		
		return (totalModules + totalResps);

	}
	
	public double getAvgRipplingProbability() {
		
		double total = 0;
		for (int i = 0; i <= indexPrimaryModules; i++) {
			for (int j = 0; j <= indexPrimaryModules; j++) {
				total = total + this.modDependencies[i][j];
			}			
		}
		
		int n = moduleView.getModules().size() * moduleView.getModules().size();
		if (n > 0)
			total = total / n;		
		return (total);
	}

	/** 
	 * This output parameter considers the average cohesion of primary modules, 
	 * and assumes a zero cohesion for all the remaining modules within the module view
	 * Precondition: This method should be invoked after 
	 * calling method estimateCohesionPrimaryModules()
	 */
	public double getAvgModuleCohesion() {
		
		double total = 0.0;
		for (int i = 0; i <= indexPrimaryModules; i++) 
			total = total + modCohesion[i];
		
		int n = moduleView.getModules().size();
		double cohesionFactor = 0.8; // Assuming non-primary modules are quite cohesive
		total = total + cohesionFactor * (n-(indexPrimaryModules +1));
		if (n > 0)
			total = total / n;
		
		return (total);
	}

	/** 
	 * This output parameter considers the average coupling of primary modules, 
	 * and assumes a zero coupling for all the remaining modules within the module view
	 * Precondition: This method should be invoked after 
	 * calling methods estimateCohesionPrimaryModules() and estimateCouplingPrimaryModules()
	 */
	public double getAvgModuleCoupling() {
		double total = 0.0;
		for (int i = 0; i <= indexPrimaryModules; i++) 
			total = total + modCoupling[i];

		int n = moduleView.getModules().size();
		if (total > 0) {
			double couplingFactor = 0.4; // Assuming non-primary modules are quite decoupled
			total = total + couplingFactor * (n-(indexPrimaryModules +1));
		}
		if (n > 0)
			total = total / n;
		
		return (total);
	}

	/** 
	 * This output parameter considers the coupling of a primary module,
	 */
	public double getModuleCoupling(ArchEModuleVO module) {
		
		int pos = this.getPrimaryModuleIndex(module);
		if (pos != -1) { // The module is a primary one
			return (modCoupling[pos]);
		}
		else // The module is any other module within the view
			return (0.0);
	}

	public double getModuleCohesion(ArchEModuleVO module) {
		
		int pos = this.getPrimaryModuleIndex(module);
		if (pos != -1) { // The module is a primary one
			return (modCohesion[pos]);
		}
		else // The module is any other module within the view
			return (0.0);
	}

	/** 
	 * This output parameter considers the coupling of a primary responsibility,
	 * based on the dependency matrix of primary responsibilities (the coupling of
	 * the remaining responsibilities within the module view is discarded)
	 */
	public double getResponsibilityCoupling(ArchEResponsibility responsibility) {
		
		int pos = this.getPrimaryResponsibilityIndex(responsibility);
		if (pos != -1) { // The responsibility is a primary one
			double total = 0.0;
			for (int i = 0; i <= indexPrimaryResponsibilities; i++) 
				total = total + respDependencies[pos][i];
			
			//int n = moduleView.getCountAllocatedResponsibilities();
			int n = allResponsibilities.getResponsibilities().size(); 
			if (n > 0)
				total = total / n;
			
			return (total);			
		}
		else // The responsibility is any other responsibility within the view
			return (0.0);
	}

	/** 
	 * This output parameter considers the average coupling of primary responsibilities, 
	 * and assumes a zero coupling for all the remaining responsibilities within 
	 * the module view
	 */
	public double getAvgResponsibilityCoupling() {
		
		double total = 0.0;
		for (int i = 0; i <= indexPrimaryResponsibilities; i++) 
			total = total + this.getResponsibilityCoupling(primaryResponsibilities[i]);
		
		//int n = moduleView.getCountAllocatedResponsibilities();
		int n = allResponsibilities.getResponsibilities().size(); 
		if (n > 0)
			total = total / n;
		
		return (total);
	}

	/** 
	 * This method returns the percentage of primary modules really
	 * affected by the change (the percentage is in the range [0..1])
	 */
	public double getRatioPrimaryModules() {

		double n = moduleView.getModules().size();
		if (n > 0)
			return ( indexPrimaryModules+1 ) / n;
		else
			return (0);

	}

	/** 
	 * This method returns the percentage of primary responsibilities really
	 * affected by the change (the percentage is in the range [0..1])
	 */
	public double getRatioPrimaryResponsibilities() {

		//int n = moduleView.getCountAllocatedResponsibilities();
		double n = allResponsibilities.getResponsibilities().size(); 
		if (n > 0)
			return ( indexPrimaryResponsibilities+1 ) / n;
		else
			return (0);
	
	}
	
	public List<ArchEResponsibility> getResponsibilities() {
		List<ArchEResponsibility> result = new ArrayList<ArchEResponsibility>();
		for (int i = 0; i <= indexPrimaryResponsibilities; i++)
			result.add(primaryResponsibilities[i]);
		//return (Arrays.asList(primaryResponsibilities));
		return (result);
	}

	public List<ArchEModuleVO> getModules() {
		List<ArchEModuleVO> result = new ArrayList<ArchEModuleVO>();
		for (int i = 0; i <= indexPrimaryModules; i++)
			result.add(primaryModules[i]);
		//return (Arrays.asList(primaryModules));
		return (result);
	}

}

