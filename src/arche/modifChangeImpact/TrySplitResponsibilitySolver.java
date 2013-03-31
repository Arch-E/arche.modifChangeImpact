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
 * This class implements the solver for the "split responsibility" tactic.
 * It searches for a target responsibility that, if splitted into two parts, 
 * can really improve the total cost of the scenario.
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
import arche.modifChangeImpact.hibernate.vo.ArchEResponsibilityDependencyRelationVO;
import arche.modifChangeImpact.hibernate.vo.ArchEResponsibilityVO;
import arche.modifChangeImpact.hibernate.vo.ArchEScenarioVO;
import arche.modifChangeImpact.hibernate.vo.ArchEVersionVO;
import edu.cmu.sei.arche.ArchEException;
import edu.cmu.sei.arche.external.data.ArchEResponsibility;
import edu.cmu.sei.arche.external.data.ArchEResponsibilityStructure;
import edu.cmu.sei.arche.external.data.ArchEScenario;

public class TrySplitResponsibilitySolver implements ModifiabilityTacticSolver {

	private static final double THRESHOLD_COST = 0.05; 
	
	private ModuleADLWrapper myModuleView;
	private ArchECoreResponsibilityStructure myResponsibilityStructure;		
	private List<ArchEResponsibility> primaryResponsibilities;
	private ArchEResponsibilityVO targetResponsibility;
	private ChangeImpactAnalyzer initialAnalyzer;
	private SplitResponsibilityChangeImpactAnalyzer bestAnalyzer;
	private SplitResponsibilityChangeImpactAnalyzer betterAnalyzer;
	private Double bestSplittingCost;
	private ArchEScenarioVO targetScenario = null;

	
	public TrySplitResponsibilitySolver(ChangeImpactAnalyzer analyzer, List<ArchEResponsibility> scenarioResponsibilities) {
		myModuleView = null;
		myResponsibilityStructure = null;
		primaryResponsibilities = scenarioResponsibilities;
		targetResponsibility = null;
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
	
	private Double findBestSplittingCost(ArchEResponsibilityVO responsibility, double maxCost) {
		
		double reductionFactor = 0.9;
		
		SplitResponsibilityChangeImpactAnalyzer newAnalyzer = new SplitResponsibilityChangeImpactAnalyzer(myModuleView, myResponsibilityStructure);
		
		newAnalyzer.setTargetResponsibility(responsibility);
		try {
			newAnalyzer.doInterpretation(primaryResponsibilities);
			newAnalyzer.doEvaluation();
		} catch (ChangeImpactAnalysisException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}				
		double totalCost = newAnalyzer.getTotalCost();
		
		if ((betterAnalyzer == null) || (totalCost < betterAnalyzer.getTotalCost()))
			betterAnalyzer = newAnalyzer;
		
		if (totalCost < reductionFactor * maxCost) {
			bestAnalyzer = newAnalyzer;
			return (totalCost);
		}
		else 
			return (null);
	}	
	
	public boolean searchForTactic(ArchEScenario scenario) {
		
		targetScenario = (ArchEScenarioVO)scenario;
		// The responsibilities are ordered according to coupling in descending order
		Comparator<ArchEResponsibility> c = new ResponsibilityCostComparator(initialAnalyzer);
//		List<ArchEResponsibility> listResponsibilities = myResponsibilityStructure.getResponsibilities();
//		List<ArchEResponsibility> listResponsibilities = initialAnalyzer.getResponsibilities();
		List<ArchEResponsibility> listResponsibilities = myResponsibilityStructure.getResponsibilitiesByScenario(scenario);
		Collections.sort(listResponsibilities, c);
		
		Iterator<ArchEResponsibility> itResponsibilities = listResponsibilities.iterator();
		
		bestAnalyzer = null;
		betterAnalyzer = null;
		targetResponsibility = null;
		double estimatedCost = 0.0;
		boolean found = false;
		boolean stop = false;
		boolean denormalizedCost = false;
		while (itResponsibilities.hasNext() && !found && !stop) {				
			targetResponsibility = (ArchEResponsibilityVO)(itResponsibilities.next());
			estimatedCost = initialAnalyzer.getResponsibilityEstimatedCost(targetResponsibility,denormalizedCost);				
			
			//System.out.println("======SEARCHING RESPONSIBILITY TO SPLIT FOR: "+targetResponsibility.getName());			
			bestSplittingCost = this.findBestSplittingCost(targetResponsibility,initialAnalyzer.getTotalCost());
			//System.out.println("               Best cost found (so far) = "+bestSplittingCost);

			if (initialAnalyzer.isPrimaryResponsibility(targetResponsibility) 
					&& (estimatedCost > THRESHOLD_COST) && bestSplittingCost != null) { 
				found = true;
				//targetResponsibility = bestAnalyzer.getTargetResponsibility();
			}

			if (estimatedCost <= THRESHOLD_COST)
				stop = true; // The remaining modules are also below the threshold
		}
		
		if (betterAnalyzer != null) { // At least there's a minimum cost found 
			found = true;
			targetResponsibility = betterAnalyzer.getTargetResponsibility();
		}
		
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
		if (targetResponsibility != null) {
			
			List parameters = new ArrayList();

			parameters.add(targetResponsibility); // parameter <0> for the question
			
			Double currentCost = initialAnalyzer.getTotalCost();		
			Double improvedCostAfterSplitting = Double.MAX_VALUE;
			if (bestAnalyzer != null)
				improvedCostAfterSplitting = bestAnalyzer.getTotalCost();
			else if (betterAnalyzer != null)
				improvedCostAfterSplitting = betterAnalyzer.getTotalCost();
			
			parameters.add(currentCost); // parameter <1> for the question
			parameters.add(improvedCostAfterSplitting); // parameter <2> for the question
			parameters.add(targetScenario);
			
			return (parameters);
		}
		else
			return (null);
	}

	public List getTarget() {
		
		List targets = new ArrayList();			
		if (targetResponsibility != null) {
			targets.add(targetResponsibility);
			return (targets);
		}
		else
			return (null);
	}

	public List estimateContext() {
		List at = new ArrayList();
		if (targetResponsibility != null)
			at.add(targetResponsibility);	
		
		return (at);
	}

	// This internal class will order responsibilities in a descending order
	// according to their individual costs
	class ResponsibilityCostComparator implements Comparator<ArchEResponsibility> {
	
		private ChangeImpactAnalyzer analyzer = null;
	
		public ResponsibilityCostComparator(ChangeImpactAnalyzer anAnalyzer) {
			analyzer = anAnalyzer;
		}

		public int compare(ArchEResponsibility resp1, ArchEResponsibility resp2) {
			double cost1 = analyzer.getResponsibilityEstimatedCost(resp1);
			double cost2 = analyzer.getResponsibilityEstimatedCost(resp2);
			if (cost1 < cost2)
				return (1);
			else if (cost1 > cost2)
				return (-1);
			else
				return (0);
		}

	}

	class SplitResponsibilityChangeImpactAnalyzer extends ChangeImpactAnalyzer {
		
	private ArchEResponsibilityVO targetResponsibility = null; // To responsibility to be split
	private int positionTarget = -1;
	private List<ArchEResponsibility> mainPrimaryResponsibilities = null;
	private List<ArchEResponsibility> newPrimaryResponsibilities = null;
	private List<ArchEModuleVO> newPrimaryModules = null; 
	private ArchEResponsibilityVO childRespA;
	private ArchEResponsibilityVO childRespB;
	private ArchEModuleVO modRespA;
	private ArchEModuleVO modRespB;

	public SplitResponsibilityChangeImpactAnalyzer(RFModuleView adl, ArchEResponsibilityStructure respStructure)  {
		super (adl, respStructure);

		ArchEVersionVO versionVO = (ArchEVersionVO)moduleView.getParent().getCurrentVersion();
		childRespA = new ArchEResponsibilityVO(versionVO); 
		childRespA.setName("internalChildRespA");
		childRespB = new ArchEResponsibilityVO(versionVO); 
		childRespB.setName("internalChildRespB");
		modRespA = new ArchEModuleVO(versionVO);
		modRespA.setName("internalChildModuleA");					
		modRespB = new ArchEModuleVO(versionVO);
		modRespB.setName("internalChildModuleB");					

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
		// This is a re-intepretation of the primary responsibilities and modules
		newPrimaryResponsibilities = new ArrayList<ArchEResponsibility>();
		for (Iterator<ArchEResponsibility> itt = mainPrimaryResponsibilities.iterator(); itt.hasNext(); )
			newPrimaryResponsibilities.add(itt.next());

		// The responsibility for the children
		double costR = ChangeImpactAnalyzer.normalizeResponsibilityCost(ChangeImpactAnalyzer.DEFAULT_RESPONSIBILITY_COST);
		super.addPrimaryResponsibility(childRespA, costR); // The first child responsibility (at position 0)
		super.addPrimaryResponsibility(childRespB, costR); // The second child responsibility (at position 1)

		costR = ChangeImpactAnalyzer.normalizeResponsibilityCost(ChangeImpactAnalyzer.DEFAULT_RESPONSIBILITY_COST);
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

		double costM = ChangeImpactAnalyzer.normalizeModuleCost(ChangeImpactAnalyzer.DEFAULT_MODULE_COST);
		super.addPrimaryModule(modRespA, costM); // The modules for the children responsibilities
		super.addPrimaryModule(modRespB, costM); 

		newPrimaryModules = computeNewRelatedPrimaryModules(newPrimaryResponsibilities);
		ArchEModuleVO modItem = null;
		for (Iterator<ArchEModuleVO> itMods = newPrimaryModules.iterator(); itMods.hasNext();) {
			modItem = itMods.next();
			costM = ChangeImpactAnalyzer.normalizeModuleCost(modItem.getCostOfChange());

			if (this.getPrimaryModuleIndex(modItem) == -1) {
//				if (!moduleView.isAllocated(targetResponsibility,modItem)) 
//					super.addPrimaryModule(modItem, costM);				
//				else if (moduleView.getResponsibilitiesByModule(modItem).size() > 1) 
					super.addPrimaryModule(modItem, costM);		
			}
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

			if (this.getPrimaryModuleIndex(modItem) == -1) {
//				if (!moduleView.isAllocated(targetResponsibility,modItem)) 
//					super.addPrimaryModule(modItem, costM);				
//				else if (moduleView.getResponsibilitiesByModule(modItem).size() > 1) 
					super.addPrimaryModule(modItem, costM);		
			}
		}

		// The position of the responsibility to be split is stored for further use
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
				if (!responsibilities.contains(temp) && !dependents.contains(temp)) 
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
	
	private boolean isOrphanModule(ArchEModuleVO module) {
		if (moduleView.isAllocated(targetResponsibility, module)) { 
			List<ArchEResponsibility> resps = moduleView.getResponsibilitiesByModule(module);
			if (resps.size() <= 1)
				return (true);
			else {
				ArchEResponsibilityVO respMine = null;
				ArchEResponsibilityVO respOthers = null;
				String relationType = ArchEResponsibilityDependencyRelationVO.class.getName();
				for (Iterator<ArchEResponsibility> itMine = resps.iterator(); itMine.hasNext();) {
					respMine = (ArchEResponsibilityVO)(itMine.next());
					for (Iterator<ArchEResponsibility> itOthers = mainPrimaryResponsibilities.iterator(); itOthers.hasNext();) {
						respOthers = (ArchEResponsibilityVO)(itOthers.next());
						if (!respMine.equals(respOthers) && !respMine.equals(targetResponsibility) 
								&& allResponsibilities.existRelation(respMine, respOthers, relationType)) {
							return (false);
						}
					}					
				}
				return (true);
			}
		}		
		return (false);		
	}

	private void updateChangeProbabilityResponsibilitiesDueToSplitting() {
		if (positionTarget > -1) { //  Update the parts of the matrix due to the splitting of the responsibility
			double probabilityOutgoing = 0.0;
			double probabilityIncoming = 0.0;
			for (int j = 2; j <= indexPrimaryResponsibilities; j++) { // The new children are at positions 0 & 1
				if (respDependencies[positionTarget][j] > 0) {
					probabilityOutgoing = probabilityOutgoing + respDependencies[positionTarget][j];
					respDependencies[0][j] = 0.50* respDependencies[positionTarget][j];
					respDependencies[1][j] = 0.50* respDependencies[positionTarget][j];
					respDependencies[positionTarget][j] = 0.0; // The value of 0.50 is necessary to be similar to that of the tactic
				}
				if (respDependencies[j][positionTarget] > 0) {
					probabilityIncoming = probabilityIncoming + respDependencies[j][positionTarget];
					respDependencies[j][0] = 0.50 * respDependencies[j][positionTarget];
					respDependencies[j][1] = 0.50 * respDependencies[j][positionTarget];
					respDependencies[j][positionTarget] = 0.0; // The value of 0.50is necessary to be similar to that of the tactic
				}
			}
			// The value of 0.45 is necessary to be similar to that of the tactic
			respDependencies[0][1] = 0.45 * DEFAULT_RIPLING_PROBABILITY_RESPONSIBILITIES;
			respDependencies[1][0] = 0.45 * DEFAULT_RIPLING_PROBABILITY_RESPONSIBILITIES;
		}
		
		return;		
	}

	private void updateChangeProbabilityModulesDueToSplitting() {

		int positionModule = -1;
		boolean becomesOrphanModule = false;
		if (positionTarget > -1) {//  Update the parts of the matrix due to the splitting of the tactic					
			for (int i = 2; i <= indexPrimaryModules; i++) {				
				
				if (moduleView.isAllocated(targetResponsibility, primaryModules[i])) {
					positionModule = i;
					// TODO: if primaryModule[i] has now no dependencies to the rest (after splitting), then its 
					// probabilities should be still zero, regardless of its allocated responsibilities
					// The condition below is not enough to detect that case
//					if (moduleView.getResponsibilitiesByModule(primaryModules[i]).size() == 1)
//						becomesOrphanModule = true;
//					else
//						becomesOrphanModule = false;
					becomesOrphanModule = this.isOrphanModule(primaryModules[i]);
					// Do updates for each possible module containing the target responsibility
					double probabilityOutgoing = 0.0;
					double probabilityIncoming = 0.0;
					for (int j = 2; j <= indexPrimaryModules; j++) { // The new children are at positions 0 & 1
						if (modDependencies[positionModule][j] > 0) {
							probabilityOutgoing = probabilityOutgoing + modDependencies[positionModule][j];
							modDependencies[0][j] = 0.50 * modDependencies[positionModule][j];
							modDependencies[1][j] = 0.50 * modDependencies[positionModule][j];
							if (becomesOrphanModule)
								modDependencies[positionModule][j] = 0.0; 
						}
						if (modDependencies[j][positionModule] > 0) {
							probabilityIncoming = probabilityIncoming + modDependencies[j][positionModule];
							modDependencies[j][0] = 0.50 * modDependencies[j][positionModule];
							modDependencies[j][1] = 0.50 * modDependencies[j][positionModule];
							if (becomesOrphanModule)
								modDependencies[j][positionModule] = 0.0; 
						}
					}
				}
			}			
			// The values of 0.7 and 0.3 are necessary to be similar to those of the tactic
			modDependencies[0][1] = respDependencies[0][1];
			modDependencies[1][0] = respDependencies[1][0];					
		}
		
		return;
	}

	// This overrides the functionality of the original method in ChangeImpactAnalyzer,
	// in order to factor in the two responsibilities resulting from the splitting
	protected void estimateCostOfChangePrimaryModules() {
		
		double costNeighbors = 0.0;
		double costAllocatedResponsibilities = 0.0;
		double count = 0;		
		ArchEResponsibility resp = null;
		
		for (int i = 2; i <= indexPrimaryModules; i++) {// The new children are at positions 0 & 1
			
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
			
			// TODO: if primaryModule[i] has now no dependencies to the rest (after splitting), then its 
			//costs should be still  zero, regardless of its allocated responsibilities
			// The condition below is not enough to detect that case
			if (this.isOrphanModule(primaryModules[i])) {
				modBasicCosts[i] = 0.0;
				costNeighbors = 0.0;
				costAllocatedResponsibilities = 0.0;
			}

			double ratio = count / (allResponsibilities.getResponsibilities().size() + 2);
			modComputedCosts[i] = ratio*modBasicCosts[i] + 0.35*costNeighbors + 0.35*costAllocatedResponsibilities;		
		
			if (modComputedCosts[i] > 1)
				modComputedCosts[i] = 1.0;
		
		}
		
		// Note: This is the cost for the children responsibilities
		count = 1;
		costNeighbors = modDependencies[1][0]* modBasicCosts[1];
		for (int j = 2; j <= indexPrimaryModules; j++) {
			if (modDependencies[j][0] > 0) {
				costNeighbors = costNeighbors + modDependencies[j][0] * modBasicCosts[j];
				count++;					
			}
		}
		if (count > 0)
			costNeighbors = costNeighbors / count;

		double costChildren = ChangeImpactAnalyzer.DEFAULT_RESPONSIBILITY_COST;
		try {
			costChildren = 0.3* targetResponsibility.getDoubleParameter(ModifChangeImpactReasoningFramework.PARAMETER_COST_OF_CHANGE);
			if (costChildren < ChangeImpactAnalyzer.MIN_RESPONSIBILITY_COST)
				costChildren = ChangeImpactAnalyzer.MIN_RESPONSIBILITY_COST;
		} catch (ArchEException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
		costAllocatedResponsibilities = ChangeImpactAnalyzer.normalizeResponsibilityCost(costChildren);
		double ratio1 = 1.0 / (allResponsibilities.getResponsibilities().size() + 2);
		modComputedCosts[0] = ratio1*ChangeImpactAnalyzer.normalizeModuleCost(ChangeImpactAnalyzer.DEFAULT_MODULE_COST) 
				+ 0.35*costNeighbors + 0.35*costAllocatedResponsibilities;
		if (modComputedCosts[0] > 1)
			modComputedCosts[0] = 1.0;

		count = 1;
		costNeighbors = modDependencies[0][1]* modBasicCosts[0];
		for (int j = 2; j <= indexPrimaryModules; j++) {
			if (modDependencies[j][1] > 0) {
				costNeighbors = costNeighbors + modDependencies[j][1] * modBasicCosts[j];
				count++;					
			}
		}
		if (count > 0)
			costNeighbors = costNeighbors / count;

		double ratio2 = 1.0 / (allResponsibilities.getResponsibilities().size() + 2);
		modComputedCosts[1] = ratio2*ChangeImpactAnalyzer.normalizeModuleCost(ChangeImpactAnalyzer.DEFAULT_MODULE_COST) 
				+ 0.35*costNeighbors + 0.35*costAllocatedResponsibilities;
		if (modComputedCosts[1] > 1)
			modComputedCosts[1] = 1.0;

		return;		
	}

	
	public void doEvaluation() {
		
		this.resetOutputParameters();		

		// These are preparatory computations to calculate the figures
		this.computeChangeProbabilityResponsibilities();
		//this.printResponsibilityDependencies();
		this.computeChangeProbabilityModules();
		//this.printModuleDependencies();
		this.updateChangeProbabilityResponsibilitiesDueToSplitting();
		//this.printResponsibilityDependencies();
		this.updateChangeProbabilityModulesDueToSplitting();
		//this.printModuleDependencies();

		// These are all the figures estimated by the analyzer (for a given class of change)
		this.estimateCostOfChangePrimaryModules();
		
		//this.printModuleEstimatedCosts();
		
		needsComputation = false;
	}

	}

}
