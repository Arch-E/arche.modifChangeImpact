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
 * This class implements the solver for the "adjust impact of refined responsibilites" tactic.
 * It searches for leaf responsibilities that, if removed from the scenario, can really improve the 
 * total cost of that scenario.
 * 
 * @author Andres Diaz-Pace
 */

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
//import java.util.logging.Level;

import arche.modifChangeImpact.hibernate.ArchECoreResponsibilityStructure;
import arche.modifChangeImpact.hibernate.vo.ArchEModuleVO;
import arche.modifChangeImpact.hibernate.vo.ArchEResponsibilityVO;
import arche.modifChangeImpact.hibernate.vo.ArchEScenarioVO;
import edu.cmu.sei.arche.ArchEException;
import edu.cmu.sei.arche.external.data.ArchEResponsibility;
import edu.cmu.sei.arche.external.data.ArchEResponsibilityStructure;
import edu.cmu.sei.arche.external.data.ArchEScenario;

public class TryAdjustImpactRefinedResponsibilitySolver implements ModifiabilityTacticSolver {

	private ModuleADLWrapper myModuleView;
	private ArchECoreResponsibilityStructure myResponsibilityStructure;		
	private List<ArchEResponsibility> primaryResponsibilities;
	private ArchEResponsibilityVO targetResponsibility;
	private ArchEResponsibilityVO leaf1, leaf2;
	private ChangeImpactAnalyzer initialAnalyzer;
	private AdjustResponsibilityRefinementChangeImpactAnalyzer bestAnalyzer;
	private AdjustResponsibilityRefinementChangeImpactAnalyzer betterAnalyzer;
	private Double bestAdjustmentCost;
	private ArchEScenarioVO currentScenario;

	
	public TryAdjustImpactRefinedResponsibilitySolver(ChangeImpactAnalyzer analyzer, List<ArchEResponsibility> scenarioResponsibilities) {
		myModuleView = null;
		myResponsibilityStructure = null;
		primaryResponsibilities = scenarioResponsibilities;
		targetResponsibility = null;
		leaf1 = null;
		leaf2 = null;
		initialAnalyzer = analyzer;
		bestAnalyzer = null;
		betterAnalyzer = null;
		currentScenario = null;
	}
	
	public void setResponsibilityStructure(ArchECoreResponsibilityStructure responsibilities) {
		myResponsibilityStructure = responsibilities;			
	}
	
	public void setModuleView(RFModuleView view) {
		myModuleView = (ModuleADLWrapper)view;			
	}
	
	private List<ArchEResponsibility> findChildrenResponsibilities(ArchEResponsibility parent) {
		List<ArchEResponsibility> result = new ArrayList<ArchEResponsibility>();
		List<ArchEResponsibility> children = myResponsibilityStructure.getChildrenResponsibilities(parent);
		ArchEResponsibilityVO respItem = null;
		for (Iterator<ArchEResponsibility> it = children.iterator(); it.hasNext();) {
			respItem = (ArchEResponsibilityVO)(it.next());
			if (myResponsibilityStructure.existTranslation(currentScenario, respItem))
				result.add(respItem);
		}
		return (result);
	}
	
	private List<ArchEResponsibility> getCopyOfResponsibilities(ArchEResponsibility deletion) {
		List<ArchEResponsibility> result = new ArrayList<ArchEResponsibility>();
		ArchEResponsibility respItem = null;
		for (Iterator<ArchEResponsibility> it = primaryResponsibilities.iterator(); it.hasNext();) {
			respItem = it.next();
			if (!respItem.equals(deletion))
				result.add(respItem);
		}
		return (result);		
	}
			
	private Double findBestAdjustmentCost(ArchEResponsibilityVO responsibility, double maxCost) {
		
		AdjustResponsibilityRefinementChangeImpactAnalyzer newAnalyzer = new AdjustResponsibilityRefinementChangeImpactAnalyzer(myModuleView, myResponsibilityStructure);
		newAnalyzer.setTargetResponsibility(responsibility);
		// Find 2 children for the targetResponsibility, and then do interpretation removing 
		// one of them from the list of primary responsibilities
		List<ArchEResponsibility> children = this.findChildrenResponsibilities(responsibility);
		if (children.size() >= 2) {
			
			leaf1 = (ArchEResponsibilityVO)(children.get(0));
			leaf2 = (ArchEResponsibilityVO)(children.get(1));
			List<ArchEResponsibility> deletion1 = this.getCopyOfResponsibilities(leaf1);
			List<ArchEResponsibility> deletion2 = this.getCopyOfResponsibilities(leaf2);
			
			try {
				newAnalyzer.doInterpretation(deletion1);
				newAnalyzer.doEvaluation();
			} catch (ChangeImpactAnalysisException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}				
			double totalCost1 = newAnalyzer.getTotalCost();
			if ((betterAnalyzer == null) || (totalCost1 < betterAnalyzer.getTotalCost()))
				betterAnalyzer = newAnalyzer;
			try {
				newAnalyzer.doInterpretation(deletion2);
				newAnalyzer.doEvaluation();
			} catch (ChangeImpactAnalysisException e) {
				// TODO Auto-generated catch block
				e.printStackTrace();
			}				
			double totalCost2 = newAnalyzer.getTotalCost();			
			if ((betterAnalyzer == null) || (totalCost2 < betterAnalyzer.getTotalCost()))
				betterAnalyzer = newAnalyzer;

			// Select the greatest cost of the two costs computed above
			if (totalCost1 < maxCost) {
				bestAnalyzer = newAnalyzer;
				return (totalCost1);
			}			
			if (totalCost2 < maxCost) {
				bestAnalyzer = newAnalyzer;
				return (totalCost2);
			}			
		}
		return (null);
	}
	
	public boolean searchForTactic(ArchEScenario scenario) {
		
		currentScenario = (ArchEScenarioVO)(scenario);
		
		// The responsibilities are ordered according to coupling in descendent order
//		List<ArchEResponsibility> listResponsibilities = myResponsibilityStructure.getResponsibilities();
//		List<ArchEResponsibility> listResponsibilities = initialAnalyzer.getResponsibilities();
		List<ArchEResponsibility> listResponsibilities = myResponsibilityStructure.getResponsibilitiesByScenario(scenario);
		
		Iterator<ArchEResponsibility> itResponsibilities = listResponsibilities.iterator();
		
		bestAnalyzer = null;
		betterAnalyzer = null;
		targetResponsibility = null;
		double estimatedCost = 0.0;
		boolean found = false;
		boolean stop = false;
		while (itResponsibilities.hasNext() && !found && !stop) {				
			targetResponsibility = (ArchEResponsibilityVO)(itResponsibilities.next());
			
			if (!myResponsibilityStructure.isLeaf(targetResponsibility)) {
				estimatedCost = initialAnalyzer.getTotalCost();				
				//System.out.println("======SEARCHING RESPONSIBILITY TO ADJUST FOR: "+targetResponsibility.getName());			
				bestAdjustmentCost = this.findBestAdjustmentCost(targetResponsibility,estimatedCost);
				//System.out.println("               Best cost found (so far) = "+bestAdjustmentCost);

				if (initialAnalyzer.isPrimaryResponsibility(targetResponsibility) && bestAdjustmentCost != null) { 
					found = true;
					//targetResponsibility = bestAnalyzer.getTargetResponsibility();
				}				
			}
		}
		
		if (betterAnalyzer != null) { // At least there's a minimum cost found 
			found = true;
			targetResponsibility = betterAnalyzer.getTargetResponsibility();
//			System.out.println("Minimum cost found (not best) = "+betterAnalyzer.getTotalCost());
		}
		
		if (found) {
//			printLog(3, Level.INFO, "Setting responsibility target --> " + targetResponsibility.getName());
			return (true);
		}
		else {
//			printLog(3, Level.INFO, "Setting responsibility target --> NOT FOUND");
			return (false);
		}
	}
	
	public List getParameters() {	
		if (targetResponsibility != null) {
			
			List parameters = new ArrayList();

			parameters.add(targetResponsibility); // parameter <0> for the question
			List<ArchEResponsibility> children = this.findChildrenResponsibilities(targetResponsibility);			
			parameters.add(children.get(0));
			parameters.add(children.get(1));		
		
			return (parameters);
		}
		else
			return (null);
	}

	public List getTarget() {
		
		List targets = new ArrayList();			
		if (targetResponsibility != null) {
			targets.add(targetResponsibility);
			List<ArchEResponsibility> children = this.findChildrenResponsibilities(targetResponsibility);			
			targets.add(children.get(0));
			targets.add(children.get(1));
			return (targets);
		}
		else
			return (null);
	}

	public List estimateContext() {
		List at = new ArrayList();
		if (targetResponsibility != null) {
			at.add(targetResponsibility);
			List<ArchEResponsibility> children = this.findChildrenResponsibilities(targetResponsibility);			
			at.add(children.get(0));
			at.add(children.get(1));
			at.add(currentScenario);
		}		
		
		return (at);
	}

	// This internal class simulates that some children responsibilities have been removed
	// from the scenario, and then estimates the resulting cost of that tactic.
	class AdjustResponsibilityRefinementChangeImpactAnalyzer extends ChangeImpactAnalyzer {
		
	private ArchEResponsibilityVO targetResponsibility = null; // To responsibility to be split
	private int positionTarget = -1;
	private List<ArchEResponsibility> mainPrimaryResponsibilities = null;
	private List<ArchEResponsibility> newPrimaryResponsibilities = null;
	private List<ArchEModuleVO> newPrimaryModules = null; 

	public AdjustResponsibilityRefinementChangeImpactAnalyzer(RFModuleView adl, ArchEResponsibilityStructure respStructure)  {
		super (adl, respStructure);
	}
	
	public void setTargetResponsibility(ArchEResponsibilityVO responsibility) {
		targetResponsibility = responsibility;		
		return;	
	}
	
	public ArchEResponsibilityVO getTargetResponsibility() {
		return (targetResponsibility);
	}

	public boolean doInterpretation(List<ArchEResponsibility> scenarioResponsibilities) 
			throws ChangeImpactAnalysisException {
		
		mainPrimaryResponsibilities = scenarioResponsibilities;
		// This is a re-interpretation of the primary responsibilities and modules
		newPrimaryResponsibilities = new ArrayList<ArchEResponsibility>();
		for (Iterator<ArchEResponsibility> itt = mainPrimaryResponsibilities.iterator(); itt.hasNext(); )
			newPrimaryResponsibilities.add(itt.next());

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

		// The position for the target responsibility is stored for further use
		positionTarget = -1;
		for (int i = 0; i <= indexPrimaryResponsibilities; i++) {
			if (primaryResponsibilities[i].equals(targetResponsibility)) 
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
			for(Iterator<ArchEResponsibility> itSec = this.deriveSecondaryResponsibilitiesFor(resp).iterator(); itSec.hasNext();) {
				temp = itSec.next();
				//System.out.println("--> Considering possible responsibility (secondary): "+temp.getName());
				if (!responsibilities.contains(temp) && !dependents.contains(temp)) 
					//System.out.println("--> Adding responsibility (dependent): "+temp.getName());
					dependents.add(temp);
			}
		}
		return (dependents);
	}
	
	private List<ArchEModuleVO> computeNewRelatedPrimaryModules(List<ArchEResponsibility> responsibilities) { 
		
		List<ArchEModuleVO> primaryModules = new ArrayList<ArchEModuleVO>();
		ArchEResponsibility resp = null;
		ArchEModuleVO mod = null;
		List<ArchEModuleVO> primaryModulesResp = null;
		boolean becomesOrphanModule = false;
		for (Iterator<ArchEResponsibility> itResps = responsibilities.iterator(); itResps.hasNext(); ) {
			resp = itResps.next();
			primaryModulesResp = moduleView.getModulesByResponsibility(resp);
			for (Iterator<ArchEModuleVO> itMods = primaryModulesResp.iterator(); itMods.hasNext();) {
				mod = itMods.next();
				becomesOrphanModule = false; // Because it only contains the responsibility to be split
//				if (resp.equals(targetResponsibility) && (moduleView.getResponsibilitiesByModule(mod).size() == 1))
//					becomesOrphanModule = true;						
				if (!primaryModules.contains(mod) && !becomesOrphanModule)
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

	public void doEvaluation() {
		
		this.resetOutputParameters();		

		// These are preparatory computations to calculate the figures
		this.computeChangeProbabilityResponsibilities();
		//this.printResponsibilityDependencies();
		this.computeChangeProbabilityModules();
		//this.printModuleDependencies();
//		this.updateChangeProbabilityResponsibilitiesDueToSplitting();
		//this.printResponsibilityDependencies();
//		this.updateChangeProbabilityModulesDueToSplitting();
		//this.printModuleDependencies();

		// These are all the figures estimated by the analyzer (for a given class of change)
		this.estimateCostOfChangePrimaryModules();
		
		//this.printModuleEstimatedCosts();
		
		needsComputation = false;
	}

	}

}

