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
 * This class implements the solver for the "insert intermediary" tactic.
 * It searches for a target responsibility that, if decoupled from the rest of 
 * the system through an intermediary, can really improve 
 * the total cost of the scenario.
 * 
 * @author Andres Diaz-Pace
 */

import java.util.ArrayList;
import java.util.Collections;
import java.util.Comparator;
import java.util.Iterator;
import java.util.List;
//import java.util.logging.Level;

import arche.modifChangeImpact.hibernate.ArchECoreResponsibilityStructure;
import arche.modifChangeImpact.hibernate.vo.ArchEModuleVO;
import arche.modifChangeImpact.hibernate.vo.ArchEResponsibilityVO;
import arche.modifChangeImpact.hibernate.vo.ArchEScenarioVO;
import arche.modifChangeImpact.hibernate.vo.ArchEVersionVO;
import edu.cmu.sei.arche.ArchEException;
import edu.cmu.sei.arche.external.data.ArchEResponsibility;
import edu.cmu.sei.arche.external.data.ArchEResponsibilityStructure;
import edu.cmu.sei.arche.external.data.ArchEScenario;

public class TryInsertIntermediaryModuleSolver implements ModifiabilityTacticSolver {

	private static final double THRESHOLD_COUPLING = 0.33; 
	
	private ModuleADLWrapper myModuleView;
	private ArchECoreResponsibilityStructure myResponsibilityStructure;		
	private List<ArchEResponsibility> primaryResponsibilities;
	private Double bestIntermediaryCost;
	private ArchEModuleVO targetModule;
	private ChangeImpactAnalyzer initialAnalyzer;
	private InsertIntermediaryChangeImpactAnalyzer bestAnalyzer;
	private InsertIntermediaryChangeImpactAnalyzer betterAnalyzer;
	private ArchEScenarioVO targetScenario;
	
	public TryInsertIntermediaryModuleSolver(ChangeImpactAnalyzer analyzer, List<ArchEResponsibility> scenarioResponsibilities) {
		myModuleView = null;
		myResponsibilityStructure = null;
		primaryResponsibilities = scenarioResponsibilities;
		targetModule = null;
		initialAnalyzer = analyzer;
		bestAnalyzer = null;
		betterAnalyzer = null;
		targetScenario = null;
	}
	
	public void setResponsibilityStructure(ArchECoreResponsibilityStructure responsibilities) {
		myResponsibilityStructure = responsibilities;			
	}
	
	public void setModuleView(RFModuleView view) {
		myModuleView = (ModuleADLWrapper)view;			
	}

	private Double optimizeIntermediaryCost(ArchEModuleVO module, double maxCost) {
		
		double guessIntermediaryCost = 1.0;
		double totalCost = 0.0;
		double costReduction = 0.9;
		
		// Try different costs for the intermediary just inserted
		InsertIntermediaryChangeImpactAnalyzer newAnalyzer = new InsertIntermediaryChangeImpactAnalyzer(myModuleView, myResponsibilityStructure);
		
		while (guessIntermediaryCost > 0.1) {
			// Compute the modifiability analysis (evaluation only) for each cost value (using the same set of
			// primary responsibilities), then compare if the response improves the actual scenario response
			newAnalyzer.setTargetModule(module, guessIntermediaryCost);
			try {
				newAnalyzer.doInterpretation(primaryResponsibilities);
				newAnalyzer.doEvaluation();
			} catch (ChangeImpactAnalysisException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}				
			totalCost = newAnalyzer.getTotalCost();
			
			if ((betterAnalyzer == null) || (totalCost < betterAnalyzer.getTotalCost()))
				betterAnalyzer = newAnalyzer;
			
			if (totalCost < costReduction*maxCost) {
				bestAnalyzer = newAnalyzer;
				return (guessIntermediaryCost);
			}
			
			guessIntermediaryCost = guessIntermediaryCost - 0.1;
		}
		return  (null);
	}
	
	public boolean searchForTactic(ArchEScenario scenario) {
		
		targetScenario = (ArchEScenarioVO)scenario;
		// The modules are ordered according to coupling in descending order
		Comparator<ArchEModuleVO> c = new ModuleCouplingComparator(initialAnalyzer);
//		List<ArchEModuleVO> listModules = myModuleView.getModules();
		List<ArchEModuleVO> listModules = initialAnalyzer.getModules();
		Collections.sort(listModules, c);
		
		Iterator<ArchEModuleVO> itModules = listModules.iterator();
		
		bestAnalyzer = null;
		betterAnalyzer = null;
		targetModule = null;
		double estimatedCoupling = 0.0;
		bestIntermediaryCost = null;
		boolean found = false;
		boolean stop = false;
		while (itModules.hasNext() && !found && !stop) {				
			targetModule = itModules.next();
			estimatedCoupling = initialAnalyzer.getModuleCoupling(targetModule);				
			//System.out.println("======SEARCHING INTERMEDIARY FOR: "+targetModule.getName());					
			bestIntermediaryCost = this.optimizeIntermediaryCost(targetModule,initialAnalyzer.getTotalCost());
			//bestIntermediaryCost = this.optimizeIntermediaryCost(targetModule, scenario.getMeasureValue());
			//System.out.println("               Best cost found (so far) = "+bestIntermediaryCost);
			
			if (initialAnalyzer.isPrimaryModule(targetModule) && (estimatedCoupling > THRESHOLD_COUPLING)
				&& (bestIntermediaryCost != null)) {
				found = true;
				//targetModule = bestAnalyzer.getTargetModule();
			}
			
			if (estimatedCoupling <= THRESHOLD_COUPLING)
				stop = true; // The remaining modules are also below the threshold
		}
		
		if (betterAnalyzer != null)
			found = true;

		// This code selects the module with the highest coupling as 
		// the one to be affected by the tactic
		if (found) {
//			printLog(3, Level.INFO, "Setting module target --> " + targetModule.getName());
			return (true);
		}
		else {
//			printLog(3, Level.INFO, "Setting module target --> NOT FOUND");
			return (false);
		}
	}
	
	public List getParameters() {	
		if (targetModule != null) {
			List parameters = new ArrayList();
			
			parameters.add(targetModule); // parameter <0> for the question
			
			Double currentCost = initialAnalyzer.getTotalCost(); 
			Double estimatedCostIntermediary = initialAnalyzer.getModuleEstimatedCost(targetModule);			
			Double improvedCostAfterInsertingIntermediary = Double.MAX_VALUE;
			if (bestAnalyzer != null) {
				improvedCostAfterInsertingIntermediary = bestAnalyzer.getTotalCost();
				estimatedCostIntermediary = ChangeImpactAnalyzer.denormalizeModuleCost(bestAnalyzer.getCostTargetModule());			
			}
			else if (betterAnalyzer != null) {
				improvedCostAfterInsertingIntermediary = betterAnalyzer.getTotalCost();
				estimatedCostIntermediary = ChangeImpactAnalyzer.denormalizeModuleCost(betterAnalyzer.getCostTargetModule());
			}
			
			parameters.add(estimatedCostIntermediary); // parameter <1> for the question
			parameters.add(currentCost); // parameter <2> for the question
			parameters.add(improvedCostAfterInsertingIntermediary); // parameter <3> for the question
			parameters.add(targetScenario);

			return (parameters);
		}
		else
			return (null);
	}

	public List getTarget() {
		
		List targets = new ArrayList();			
		if (targetModule != null) {
			targets.add(targetModule);
			return (targets);
		}
		else
			return (null);
	}

	public List estimateContext() {		
		List at = new ArrayList();
		if (targetModule != null)
			at.add(targetModule);
		
		return (at);
	}


	// This internal class will order modules in a descending order
	// according to their average coupling
	class ModuleCouplingComparator implements Comparator<ArchEModuleVO> {
	
		private ChangeImpactAnalyzer analyzer = null;
	
		public ModuleCouplingComparator(ChangeImpactAnalyzer anAnalyzer) {
			analyzer = anAnalyzer;
		}

		public int compare(ArchEModuleVO mod1, ArchEModuleVO mod2) {
			double coupling1 = analyzer.getModuleCoupling(mod1);
			double coupling2 = analyzer.getModuleCoupling(mod2);
			if (coupling1 < coupling2)
				return (1);
			else if (coupling1 > coupling2)
				return (-1);
			else
				return (0);
		}

	}

	class InsertIntermediaryChangeImpactAnalyzer extends ChangeImpactAnalyzer {
	
	private ArchEModuleVO targetModule = null; // To module on which the intermediary is inserted
	private int positionTarget = -1;
	private double costIntermediary;
	private List<ArchEResponsibility> mainPrimaryResponsibilities = null;
	private List<ArchEResponsibility> newPrimaryResponsibilities = null;
	private List<ArchEModuleVO> newPrimaryModules = null; 
	private List<ArchEModuleVO> decoupledModules = null;
	private ArchEResponsibilityVO intermediaryResp;
	private ArchEModuleVO intermediaryMod;

	// This internal class simulates that the intermediary is inserted,
	// and then estimates the resulting cost of that tactic.
	public InsertIntermediaryChangeImpactAnalyzer(RFModuleView adl,	ArchEResponsibilityStructure respStructure)  {
		super (adl, respStructure);

		ArchEVersionVO versionVO = (ArchEVersionVO)moduleView.getParent().getCurrentVersion();
		intermediaryResp = new ArchEResponsibilityVO(versionVO); 
		intermediaryResp.setName("internalResponsibility");
		intermediaryMod = new ArchEModuleVO(versionVO);
		intermediaryMod.setName("internalModule");					

	}
	
	public void setTargetModule(ArchEModuleVO module, double cost) {
		targetModule = module;
		costIntermediary = cost; //normalizeModuleCost(cost);

		decoupledModules = new ArrayList<ArchEModuleVO>(); // All the modules related to the target module directly
		ArchEModuleVO modItem = null;
		for (Iterator<ArchEModuleVO> it = moduleView.getModules().iterator(); it.hasNext();) {
			modItem = it.next();
			if (!modItem.equals(targetModule)&& (moduleView.hasDependency(targetModule, modItem)))
				decoupledModules.add(modItem);
		}	
		
		return;		
	}
	
	public ArchEModuleVO getTargetModule() {
		return (targetModule);
	}
	
	public double getCostTargetModule() {
		return (costIntermediary);
	}

	public boolean doInterpretation(List<ArchEResponsibility> scenarioResponsibilities) 
			throws ChangeImpactAnalysisException {
		
		mainPrimaryResponsibilities = scenarioResponsibilities;
		// This is a re-interpretation of the primary responsibilities and modules
		newPrimaryResponsibilities = new ArrayList<ArchEResponsibility>();
		for (Iterator<ArchEResponsibility> itt = mainPrimaryResponsibilities.iterator(); itt.hasNext(); )
			newPrimaryResponsibilities.add(itt.next());

		// The responsibility for the intermediary
		super.addPrimaryResponsibility(intermediaryResp, ChangeImpactAnalyzer.normalizeResponsibilityCost(ChangeImpactAnalyzer.DEPENDENT_RESPONSIBILITY_COST)); 

		double costR = ChangeImpactAnalyzer.normalizeResponsibilityCost(ChangeImpactAnalyzer.DEFAULT_RESPONSIBILITY_COST);
		ArchEResponsibility respItem = null;
		for (Iterator<ArchEResponsibility> itResps = newPrimaryResponsibilities.iterator(); itResps.hasNext();) {
			respItem = itResps.next();
			try {
				costR = respItem.getDoubleParameter(ModifChangeImpactReasoningFramework.PARAMETER_COST_OF_CHANGE);
				costR = ChangeImpactAnalyzer.normalizeResponsibilityCost(costR);
			} catch (ArchEException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}
			super.addPrimaryResponsibility(respItem, costR);
		}

		boolean added = super.addPrimaryModule(intermediaryMod, costIntermediary); // The module for the intermediary

		newPrimaryModules = computeNewRelatedPrimaryModules(newPrimaryResponsibilities);
		double costM = ChangeImpactAnalyzer.normalizeModuleCost(ChangeImpactAnalyzer.DEFAULT_MODULE_COST);
		ArchEModuleVO modItem = null;
		for (Iterator<ArchEModuleVO> itMods = newPrimaryModules.iterator(); itMods.hasNext();) {
			modItem = itMods.next();
			costM = ChangeImpactAnalyzer.normalizeModuleCost(modItem.getCostOfChange());
			if (this.getPrimaryModuleIndex(modItem) == -1)
				super.addPrimaryModule(modItem, costM);
		}

		List<ArchEResponsibility> temp = computeNewDependentResponsibilities(mainPrimaryResponsibilities);
		newPrimaryResponsibilities.addAll(temp);
		costR = ChangeImpactAnalyzer.normalizeResponsibilityCost(ChangeImpactAnalyzer.DEPENDENT_RESPONSIBILITY_COST);
		respItem = null;
		for (Iterator<ArchEResponsibility> itResps = temp.iterator(); itResps.hasNext();) {
			respItem = itResps.next();	
			if (this.getPrimaryResponsibilityIndex(respItem) == -1)
				super.addPrimaryResponsibility(respItem, costR);
		}
			
		newPrimaryModules = computeNewRelatedPrimaryModules(newPrimaryResponsibilities);
		
		temp = computeNewInferredResponsibilities(newPrimaryResponsibilities, newPrimaryModules);
		newPrimaryResponsibilities.addAll(temp);
		costR = ChangeImpactAnalyzer.normalizeResponsibilityCost(ChangeImpactAnalyzer.DEPENDENT_RESPONSIBILITY_COST);
		respItem = null;
		for (Iterator<ArchEResponsibility> itResps = temp.iterator(); itResps.hasNext();) {
			respItem = itResps.next();			
			if (this.getPrimaryResponsibilityIndex(respItem) == -1)
				super.addPrimaryResponsibility(respItem, costR);
		}

		costM = ChangeImpactAnalyzer.normalizeModuleCost(ChangeImpactAnalyzer.DEPENDENT_MODULE_COST);
		modItem = null;
		for (Iterator<ArchEModuleVO> itMods = newPrimaryModules.iterator(); itMods.hasNext();) {
			modItem = itMods.next();
			costM = ChangeImpactAnalyzer.normalizeModuleCost(modItem.getCostOfChange());
			if (this.getPrimaryModuleIndex(modItem) == -1)
				super.addPrimaryModule(modItem, costM);
		}

		// The position of the target module is stored for further use
		positionTarget = -1;
		for (int i = 0; i <= indexPrimaryModules; i++) {
			if (primaryModules[i].equals(targetModule)) 
				positionTarget = i;
		}		

		return (true);
	}

	private List<ArchEResponsibility> computeNewDependentResponsibilities(List<ArchEResponsibility> responsibilities) {
		// It adds a number of "dependent" responsibilities to the scope of primary responsibilities
		List<ArchEResponsibility> dependents = new ArrayList<ArchEResponsibility>();
		ArchEResponsibility resp = null;
		ArchEResponsibility temp = null;
		for (Iterator<ArchEResponsibility> it = responsibilities.iterator(); it.hasNext();) {
			resp = it.next();
			if (!moduleView.isAllocated(resp, targetModule)) {
				for(Iterator<ArchEResponsibility> itSec = this.deriveSecondaryResponsibilitiesFor(resp).iterator(); itSec.hasNext();) {
					temp = itSec.next();
					if (!responsibilities.contains(temp) // If filters out responsibilities allocated to modules related to the target module directly
							&& !dependents.contains(temp) && !isNeighborResponsibility(temp))
						dependents.add(temp);
				}					
			}
		}
		return (dependents);
	}
	
	private boolean isNeighborResponsibility(ArchEResponsibility responsibility) {
		
		for (Iterator<ArchEModuleVO> it = decoupledModules.iterator(); it.hasNext();) {
			if (moduleView.isAllocated(responsibility, it.next()))
					return (true);
		}
		return (false);
	}

	private List<ArchEModuleVO> computeNewRelatedPrimaryModules(List<ArchEResponsibility> responsibilities) { 
		
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
	
	private List<ArchEResponsibility> computeNewInferredResponsibilities(List<ArchEResponsibility> responsibilities, List<ArchEModuleVO> modules) {
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

	private void updateChangeProbabilityModulesDueToIntermediary() {
		
		if (positionTarget > -1) { //  Update the parts of the matrix due to the insertion of the intermediary
			double probabilityOutgoing = 0.0;
			double probabilityIncoming = 0.0;
			for (int j = 1; j <= indexPrimaryModules; j++) { // The intermediary module is at position 0
				if (modDependencies[positionTarget][j] > 0) {
					probabilityOutgoing = probabilityOutgoing + modDependencies[positionTarget][j];
					modDependencies[0][j] = 0.75* modDependencies[positionTarget][j];
					modDependencies[positionTarget][j] = 0.0; // The value of 0.75 is necessary to be similar to that of the tactic
				}
				if (modDependencies[j][positionTarget] > 0) {
					probabilityIncoming = probabilityIncoming + modDependencies[j][positionTarget];
					modDependencies[j][0] = 0.75* modDependencies[j][positionTarget];
					modDependencies[j][positionTarget] = 0.0; // The value of 0.75 is necessary to be similar to that of the tactic
				}
			}
			// The values of 0.7 and 0.3 are necessary to be similar to those of the tactic
			modDependencies[positionTarget][0] = 0.7 * DEFAULT_RIPLING_PROBABILITY_RESPONSIBILITIES;
			modDependencies[0][positionTarget] = 0.3 * DEFAULT_RIPLING_PROBABILITY_RESPONSIBILITIES;
		}
		
		return;
	}

	// This overrides the functionality of the original method in ChangeImpactAnalyzer,
	// in order to factor in the insertion of the target intermediary
	protected void estimateCostOfChangePrimaryModules() {
		
		double costNeighbors = 0.0;
		double costAllocatedResponsibilities = 0.0;
		double count = 0;		
		ArchEResponsibility resp = null;
		
		for (int i = 1; i <= indexPrimaryModules; i++) {// The intermediary module is at position 0
			
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
			
			double ratio = count / (allResponsibilities.getResponsibilities().size() + 1);
			modComputedCosts[i] = ratio*modBasicCosts[i] + 0.35*costNeighbors + 0.35*costAllocatedResponsibilities;
			if (modComputedCosts[i] > 1)
				modComputedCosts[i] = 1.0;
		
		}
		
		count = 0;
		costNeighbors = 0.0;
		for (int j = 1; j <= indexPrimaryModules; j++) {
			if (modDependencies[j][0] > 0) {
				costNeighbors = costNeighbors + modDependencies[j][0] * modBasicCosts[j];
				count++;					
			}
		}
		if (count > 0)
			costNeighbors = costNeighbors / count;

		costAllocatedResponsibilities = ChangeImpactAnalyzer.normalizeResponsibilityCost(ChangeImpactAnalyzer.DEPENDENT_RESPONSIBILITY_COST);
		double ratio1 = 1.0 / (allResponsibilities.getResponsibilities().size() + 1);
		modComputedCosts[0] = ratio1*costIntermediary + 0.35*costNeighbors + 0.35*costAllocatedResponsibilities;
		if (modComputedCosts[0] > 1)
			modComputedCosts[0] = 1.0;

		return;		
	}

	
	public void doEvaluation() {
		
		this.resetOutputParameters();		

		// These are preparatory computations to calculate the figures
		this.computeChangeProbabilityResponsibilities();
		//this.printResponsibilityDependencies();
		this.computeChangeProbabilityModules();
		//this.printModuleDependencies();
		this.updateChangeProbabilityModulesDueToIntermediary();
		//this.printModuleDependencies();

		// These are all the figures estimated by the analyzer (for a given class of change)
		this.estimateCostOfChangePrimaryModules();
		
		//this.printModuleEstimatedCosts();
		
		needsComputation = false;
	}

	}

}